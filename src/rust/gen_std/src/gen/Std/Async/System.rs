// Lean compiler output
// Module: Std.Async.System
// Imports: Std.Time Std.Internal.UV.System Std.Data.HashMap
use crate::ffi::{
    lean_array_get_size, lean_array_size, lean_array_to_list, lean_array_uget_borrowed,
    lean_array_uset, lean_int_dec_eq, lean_mk_array, lean_nat_dec_eq, lean_nat_dec_lt,
    lean_nat_div, lean_nat_mul, lean_nat_to_int, lean_string_dec_eq, lean_string_length,
    lean_uint64_of_nat, lean_uint64_to_nat, lean_usize_add, lean_usize_dec_eq, lean_usize_dec_lt,
    lean_usize_of_nat, lean_usize_sub, lean_uv_cpu_info, lean_uv_hrtime, lean_uv_os_environ,
    lean_uv_os_get_group, lean_uv_os_get_passwd, lean_uv_os_getenv, lean_uv_os_gethostname,
    lean_uv_os_homedir, lean_uv_os_setenv, lean_uv_os_tmpdir, lean_uv_os_uname,
    lean_uv_os_unsetenv, lean_uv_uptime,
};
use crate::r#gen::Init::Control::Basic::l_instForInOfForIn_x27___redArg___lam__1;
use crate::r#gen::Init::Control::Id::{
    l_Id_instMonad___lam__0, l_Id_instMonad___lam__1___boxed, l_Id_instMonad___lam__2___boxed,
    l_Id_instMonad___lam__3, l_Id_instMonad___lam__4___boxed, l_Id_instMonad___lam__5___boxed,
    l_Id_instMonad___lam__6,
};
use crate::r#gen::Init::Data::Array::Basic::l_Array_instForIn_x27InferInstanceMembershipOfMonad___redArg___lam__0;
use crate::r#gen::Init::Data::Format::Basic::l_Std_Format_fill;
use crate::r#gen::Init::Data::List::Basic::l_List_reverse___redArg;
use crate::r#gen::Init::Data::Nat::Power2::Basic::l_Nat_nextPowerOfTwo;
use crate::r#gen::Init::Data::Option::Basic::l_Option_instDecidableEq___redArg;
use crate::r#gen::Init::Data::Rat::Basic::l_Rat_ofInt;
use crate::r#gen::Init::Data::Repr::{l_Nat_reprFast, l_Repr_addAppParen, l_String_quote};
use crate::r#gen::Init::Prelude::{
    l_String_hash___boxed, l_instBEqOfDecidableEq___redArg___lam__0___boxed,
    l_instDecidableEqString___boxed,
};
use crate::r#gen::Init::System::FilePath::l_System_instDecidableEqFilePath___boxed;
use crate::r#gen::Std::Data::DHashMap::Internal::Defs::{
    l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___redArg,
    l_Std_DHashMap_Internal_Raw_u2080_Const_insertMany___redArg,
};
use crate::r#gen::Std::Data::HashMap::{
    initialize_Std_Data_HashMap, runtime_initialize_Std_Data_HashMap,
};
use crate::r#gen::Std::Internal::UV::System::{
    initialize_Std_Internal_UV_System, runtime_initialize_Std_Internal_UV_System,
};
use crate::r#gen::Std::Time::Time::Unit::Millisecond::{
    l_Std_Time_Millisecond_instInhabitedOffset, l_Std_Time_Millisecond_instReprOrdinal___lam__0,
};
use crate::r#gen::Std::Time::{initialize_Std_Time, runtime_initialize_Std_Time};
pub static mut l_Std_Async_System_instInhabitedGroupId_default: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static mut l_Std_Async_System_instInhabitedGroupId: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Std_Async_System_instOrdGroupId___closed__0_value: crate::leanh::LeanClosureObject<0> =
    crate::leanh::LeanClosureObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 0)
                as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Std_Async_System_instOrdGroupId_ord___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Std_Async_System_instOrdGroupId___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Async_System_instOrdGroupId___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Std_Async_System_instOrdGroupId: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Async_System_instOrdGroupId___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Async_System_instReprGroupId___lam__0___closed__0_value:
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
    m_data: [71, 114, 111, 117, 112, 73, 100, 46, 109, 107, 32, 0],
};
static mut l_Std_Async_System_instReprGroupId___lam__0___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Async_System_instReprGroupId___lam__0___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Async_System_instReprGroupId___lam__0___closed__1_value:
    crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [
        core::ptr::addr_of!(l_Std_Async_System_instReprGroupId___lam__0___closed__0_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Std_Async_System_instReprGroupId___lam__0___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Async_System_instReprGroupId___lam__0___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Async_System_instReprGroupId___closed__0_value: crate::leanh::LeanClosureObject<
    0,
> = crate::leanh::LeanClosureObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Std_Async_System_instReprGroupId___lam__0___boxed as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Std_Async_System_instReprGroupId___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Async_System_instReprGroupId___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Std_Async_System_instReprGroupId: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Async_System_instReprGroupId___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Std_Async_System_instInhabitedUserId_default: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static mut l_Std_Async_System_instInhabitedUserId: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Std_Async_System_instOrdUserId___closed__0_value: crate::leanh::LeanClosureObject<0> =
    crate::leanh::LeanClosureObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 0)
                as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Std_Async_System_instOrdUserId_ord___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Std_Async_System_instOrdUserId___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Async_System_instOrdUserId___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Std_Async_System_instOrdUserId: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Async_System_instOrdUserId___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Async_System_instReprUserId___lam__0___closed__0_value:
    crate::leanh::LeanStringObject<11> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 11,
    m_capacity: 11,
    m_length: 10,
    m_data: [85, 115, 101, 114, 73, 100, 46, 109, 107, 32, 0],
};
static mut l_Std_Async_System_instReprUserId___lam__0___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Async_System_instReprUserId___lam__0___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Async_System_instReprUserId___lam__0___closed__1_value:
    crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [
        core::ptr::addr_of!(l_Std_Async_System_instReprUserId___lam__0___closed__0_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Std_Async_System_instReprUserId___lam__0___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Async_System_instReprUserId___lam__0___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Async_System_instReprUserId___closed__0_value: crate::leanh::LeanClosureObject<0> =
    crate::leanh::LeanClosureObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 0)
                as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Std_Async_System_instReprUserId___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Std_Async_System_instReprUserId___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Async_System_instReprUserId___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Std_Async_System_instReprUserId: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Async_System_instReprUserId___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Async_System_instInhabitedSystemUser_default___closed__0_value:
    crate::leanh::LeanStringObject<1> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
static mut l_Std_Async_System_instInhabitedSystemUser_default___closed__0:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Async_System_instInhabitedSystemUser_default___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Async_System_instInhabitedSystemUser_default___closed__1_value:
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
        core::ptr::addr_of!(l_Std_Async_System_instInhabitedSystemUser_default___closed__0_value)
            as *mut crate::leanh::LeanObject,
        (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
        (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
        (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
        (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Std_Async_System_instInhabitedSystemUser_default___closed__1:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Async_System_instInhabitedSystemUser_default___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Std_Async_System_instInhabitedSystemUser_default: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Async_System_instInhabitedSystemUser_default___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Std_Async_System_instInhabitedSystemUser: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Async_System_instInhabitedSystemUser_default___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Option_repr___at___00Std_Async_System_instReprSystemUser_repr_spec__0___closed__0_value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [110, 111, 110, 101, 0]};
static mut l_Option_repr___at___00Std_Async_System_instReprSystemUser_repr_spec__0___closed__0:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Option_repr___at___00Std_Async_System_instReprSystemUser_repr_spec__0___closed__0_value
) as *mut crate::leanh::LeanObject;
pub static l_Option_repr___at___00Std_Async_System_instReprSystemUser_repr_spec__0___closed__1_value: crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 3 }, m_objs: [core::ptr::addr_of!(l_Option_repr___at___00Std_Async_System_instReprSystemUser_repr_spec__0___closed__0_value) as *mut crate::leanh::LeanObject] };
static mut l_Option_repr___at___00Std_Async_System_instReprSystemUser_repr_spec__0___closed__1:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Option_repr___at___00Std_Async_System_instReprSystemUser_repr_spec__0___closed__1_value
) as *mut crate::leanh::LeanObject;
pub static l_Option_repr___at___00Std_Async_System_instReprSystemUser_repr_spec__0___closed__2_value: crate::leanh::LeanStringObject<6> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [115, 111, 109, 101, 32, 0]};
static mut l_Option_repr___at___00Std_Async_System_instReprSystemUser_repr_spec__0___closed__2:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Option_repr___at___00Std_Async_System_instReprSystemUser_repr_spec__0___closed__2_value
) as *mut crate::leanh::LeanObject;
pub static l_Option_repr___at___00Std_Async_System_instReprSystemUser_repr_spec__0___closed__3_value: crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 3 }, m_objs: [core::ptr::addr_of!(l_Option_repr___at___00Std_Async_System_instReprSystemUser_repr_spec__0___closed__2_value) as *mut crate::leanh::LeanObject] };
static mut l_Option_repr___at___00Std_Async_System_instReprSystemUser_repr_spec__0___closed__3:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Option_repr___at___00Std_Async_System_instReprSystemUser_repr_spec__0___closed__3_value
) as *mut crate::leanh::LeanObject;
pub static l_Option_repr___at___00Std_Async_System_instReprSystemUser_repr_spec__3___closed__0_value: crate::leanh::LeanStringObject<13> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 13, m_capacity: 13, m_length: 12, m_data: [70, 105, 108, 101, 80, 97, 116, 104, 46, 109, 107, 32, 0]};
static mut l_Option_repr___at___00Std_Async_System_instReprSystemUser_repr_spec__3___closed__0:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Option_repr___at___00Std_Async_System_instReprSystemUser_repr_spec__3___closed__0_value
) as *mut crate::leanh::LeanObject;
pub static l_Option_repr___at___00Std_Async_System_instReprSystemUser_repr_spec__3___closed__1_value: crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 3 }, m_objs: [core::ptr::addr_of!(l_Option_repr___at___00Std_Async_System_instReprSystemUser_repr_spec__3___closed__0_value) as *mut crate::leanh::LeanObject] };
static mut l_Option_repr___at___00Std_Async_System_instReprSystemUser_repr_spec__3___closed__1:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Option_repr___at___00Std_Async_System_instReprSystemUser_repr_spec__3___closed__1_value
) as *mut crate::leanh::LeanObject;
pub static l_Std_Async_System_instReprSystemUser_repr___redArg___closed__0_value:
    crate::leanh::LeanStringObject<3> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
static mut l_Std_Async_System_instReprSystemUser_repr___redArg___closed__0:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Async_System_instReprSystemUser_repr___redArg___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Async_System_instReprSystemUser_repr___redArg___closed__1_value:
    crate::leanh::LeanStringObject<9> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
static mut l_Std_Async_System_instReprSystemUser_repr___redArg___closed__1:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Async_System_instReprSystemUser_repr___redArg___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Async_System_instReprSystemUser_repr___redArg___closed__2_value:
    crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [core::ptr::addr_of!(
        l_Std_Async_System_instReprSystemUser_repr___redArg___closed__1_value
    ) as *mut crate::leanh::LeanObject],
};
static mut l_Std_Async_System_instReprSystemUser_repr___redArg___closed__2:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Async_System_instReprSystemUser_repr___redArg___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Async_System_instReprSystemUser_repr___redArg___closed__3_value:
    crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 5,
    },
    m_objs: [
        (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Std_Async_System_instReprSystemUser_repr___redArg___closed__2_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Std_Async_System_instReprSystemUser_repr___redArg___closed__3:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Async_System_instReprSystemUser_repr___redArg___closed__3_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Async_System_instReprSystemUser_repr___redArg___closed__4_value:
    crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
static mut l_Std_Async_System_instReprSystemUser_repr___redArg___closed__4:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Async_System_instReprSystemUser_repr___redArg___closed__4_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Async_System_instReprSystemUser_repr___redArg___closed__5_value:
    crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [core::ptr::addr_of!(
        l_Std_Async_System_instReprSystemUser_repr___redArg___closed__4_value
    ) as *mut crate::leanh::LeanObject],
};
static mut l_Std_Async_System_instReprSystemUser_repr___redArg___closed__5:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Async_System_instReprSystemUser_repr___redArg___closed__5_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Async_System_instReprSystemUser_repr___redArg___closed__6_value:
    crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 5,
    },
    m_objs: [
        core::ptr::addr_of!(l_Std_Async_System_instReprSystemUser_repr___redArg___closed__3_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Std_Async_System_instReprSystemUser_repr___redArg___closed__5_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Std_Async_System_instReprSystemUser_repr___redArg___closed__6:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Async_System_instReprSystemUser_repr___redArg___closed__6_value)
        as *mut crate::leanh::LeanObject;
static mut l_Std_Async_System_instReprSystemUser_repr___redArg___closed__7_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_Async_System_instReprSystemUser_repr___redArg___closed__7:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Std_Async_System_instReprSystemUser_repr___redArg___closed__8_value:
    crate::leanh::LeanStringObject<2> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
static mut l_Std_Async_System_instReprSystemUser_repr___redArg___closed__8:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Async_System_instReprSystemUser_repr___redArg___closed__8_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Async_System_instReprSystemUser_repr___redArg___closed__9_value:
    crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [core::ptr::addr_of!(
        l_Std_Async_System_instReprSystemUser_repr___redArg___closed__8_value
    ) as *mut crate::leanh::LeanObject],
};
static mut l_Std_Async_System_instReprSystemUser_repr___redArg___closed__9:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Async_System_instReprSystemUser_repr___redArg___closed__9_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Async_System_instReprSystemUser_repr___redArg___closed__10_value:
    crate::leanh::LeanStringObject<7> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 7,
    m_capacity: 7,
    m_length: 6,
    m_data: [117, 115, 101, 114, 73, 100, 0],
};
static mut l_Std_Async_System_instReprSystemUser_repr___redArg___closed__10:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Async_System_instReprSystemUser_repr___redArg___closed__10_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Async_System_instReprSystemUser_repr___redArg___closed__11_value:
    crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [core::ptr::addr_of!(
        l_Std_Async_System_instReprSystemUser_repr___redArg___closed__10_value
    ) as *mut crate::leanh::LeanObject],
};
static mut l_Std_Async_System_instReprSystemUser_repr___redArg___closed__11:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Async_System_instReprSystemUser_repr___redArg___closed__11_value)
        as *mut crate::leanh::LeanObject;
static mut l_Std_Async_System_instReprSystemUser_repr___redArg___closed__12_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_Async_System_instReprSystemUser_repr___redArg___closed__12:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Std_Async_System_instReprSystemUser_repr___redArg___closed__13_value:
    crate::leanh::LeanStringObject<8> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 8,
    m_capacity: 8,
    m_length: 7,
    m_data: [103, 114, 111, 117, 112, 73, 100, 0],
};
static mut l_Std_Async_System_instReprSystemUser_repr___redArg___closed__13:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Async_System_instReprSystemUser_repr___redArg___closed__13_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Async_System_instReprSystemUser_repr___redArg___closed__14_value:
    crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [core::ptr::addr_of!(
        l_Std_Async_System_instReprSystemUser_repr___redArg___closed__13_value
    ) as *mut crate::leanh::LeanObject],
};
static mut l_Std_Async_System_instReprSystemUser_repr___redArg___closed__14:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Async_System_instReprSystemUser_repr___redArg___closed__14_value)
        as *mut crate::leanh::LeanObject;
static mut l_Std_Async_System_instReprSystemUser_repr___redArg___closed__15_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_Async_System_instReprSystemUser_repr___redArg___closed__15:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Std_Async_System_instReprSystemUser_repr___redArg___closed__16_value:
    crate::leanh::LeanStringObject<6> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
static mut l_Std_Async_System_instReprSystemUser_repr___redArg___closed__16:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Async_System_instReprSystemUser_repr___redArg___closed__16_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Async_System_instReprSystemUser_repr___redArg___closed__17_value:
    crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [core::ptr::addr_of!(
        l_Std_Async_System_instReprSystemUser_repr___redArg___closed__16_value
    ) as *mut crate::leanh::LeanObject],
};
static mut l_Std_Async_System_instReprSystemUser_repr___redArg___closed__17:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Async_System_instReprSystemUser_repr___redArg___closed__17_value)
        as *mut crate::leanh::LeanObject;
static mut l_Std_Async_System_instReprSystemUser_repr___redArg___closed__18_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_Async_System_instReprSystemUser_repr___redArg___closed__18:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Std_Async_System_instReprSystemUser_repr___redArg___closed__19_value:
    crate::leanh::LeanStringObject<8> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 8,
    m_capacity: 8,
    m_length: 7,
    m_data: [104, 111, 109, 101, 68, 105, 114, 0],
};
static mut l_Std_Async_System_instReprSystemUser_repr___redArg___closed__19:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Async_System_instReprSystemUser_repr___redArg___closed__19_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Async_System_instReprSystemUser_repr___redArg___closed__20_value:
    crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [core::ptr::addr_of!(
        l_Std_Async_System_instReprSystemUser_repr___redArg___closed__19_value
    ) as *mut crate::leanh::LeanObject],
};
static mut l_Std_Async_System_instReprSystemUser_repr___redArg___closed__20:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Async_System_instReprSystemUser_repr___redArg___closed__20_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Async_System_instReprSystemUser_repr___redArg___closed__21_value:
    crate::leanh::LeanStringObject<3> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
static mut l_Std_Async_System_instReprSystemUser_repr___redArg___closed__21:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Async_System_instReprSystemUser_repr___redArg___closed__21_value)
        as *mut crate::leanh::LeanObject;
static mut l_Std_Async_System_instReprSystemUser_repr___redArg___closed__22_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_Async_System_instReprSystemUser_repr___redArg___closed__22:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Std_Async_System_instReprSystemUser_repr___redArg___closed__23_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_Async_System_instReprSystemUser_repr___redArg___closed__23:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Std_Async_System_instReprSystemUser_repr___redArg___closed__24_value:
    crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [core::ptr::addr_of!(
        l_Std_Async_System_instReprSystemUser_repr___redArg___closed__0_value
    ) as *mut crate::leanh::LeanObject],
};
static mut l_Std_Async_System_instReprSystemUser_repr___redArg___closed__24:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Async_System_instReprSystemUser_repr___redArg___closed__24_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Async_System_instReprSystemUser_repr___redArg___closed__25_value:
    crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [core::ptr::addr_of!(
        l_Std_Async_System_instReprSystemUser_repr___redArg___closed__21_value
    ) as *mut crate::leanh::LeanObject],
};
static mut l_Std_Async_System_instReprSystemUser_repr___redArg___closed__25:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Async_System_instReprSystemUser_repr___redArg___closed__25_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Async_System_instReprSystemUser___closed__0_value:
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
    m_fun: l_Std_Async_System_instReprSystemUser_repr___boxed as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Std_Async_System_instReprSystemUser___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Async_System_instReprSystemUser___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Std_Async_System_instReprSystemUser: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Async_System_instReprSystemUser___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Array_repr___at___00Std_Async_System_instReprGroupInfo_repr_spec__0___closed__0_value: crate::leanh::LeanStringObject<3> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 3, m_capacity: 3, m_length: 2, m_data: [35, 91, 0]};
static mut l_Array_repr___at___00Std_Async_System_instReprGroupInfo_repr_spec__0___closed__0:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Array_repr___at___00Std_Async_System_instReprGroupInfo_repr_spec__0___closed__0_value
) as *mut crate::leanh::LeanObject;
pub static l_Array_repr___at___00Std_Async_System_instReprGroupInfo_repr_spec__0___closed__1_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 5 }, m_objs: [core::ptr::addr_of!(l_Std_Async_System_instReprSystemUser_repr___redArg___closed__9_value) as *mut crate::leanh::LeanObject,((( 1 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l_Array_repr___at___00Std_Async_System_instReprGroupInfo_repr_spec__0___closed__1:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Array_repr___at___00Std_Async_System_instReprGroupInfo_repr_spec__0___closed__1_value
) as *mut crate::leanh::LeanObject;
pub static l_Array_repr___at___00Std_Async_System_instReprGroupInfo_repr_spec__0___closed__2_value: crate::leanh::LeanStringObject<2> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [93, 0]};
static mut l_Array_repr___at___00Std_Async_System_instReprGroupInfo_repr_spec__0___closed__2:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Array_repr___at___00Std_Async_System_instReprGroupInfo_repr_spec__0___closed__2_value
) as *mut crate::leanh::LeanObject;
static mut l_Array_repr___at___00Std_Async_System_instReprGroupInfo_repr_spec__0___closed__3_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Array_repr___at___00Std_Async_System_instReprGroupInfo_repr_spec__0___closed__3:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Array_repr___at___00Std_Async_System_instReprGroupInfo_repr_spec__0___closed__4_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Array_repr___at___00Std_Async_System_instReprGroupInfo_repr_spec__0___closed__4:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Array_repr___at___00Std_Async_System_instReprGroupInfo_repr_spec__0___closed__5_value: crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 3 }, m_objs: [core::ptr::addr_of!(l_Array_repr___at___00Std_Async_System_instReprGroupInfo_repr_spec__0___closed__0_value) as *mut crate::leanh::LeanObject] };
static mut l_Array_repr___at___00Std_Async_System_instReprGroupInfo_repr_spec__0___closed__5:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Array_repr___at___00Std_Async_System_instReprGroupInfo_repr_spec__0___closed__5_value
) as *mut crate::leanh::LeanObject;
pub static l_Array_repr___at___00Std_Async_System_instReprGroupInfo_repr_spec__0___closed__6_value: crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 3 }, m_objs: [core::ptr::addr_of!(l_Array_repr___at___00Std_Async_System_instReprGroupInfo_repr_spec__0___closed__2_value) as *mut crate::leanh::LeanObject] };
static mut l_Array_repr___at___00Std_Async_System_instReprGroupInfo_repr_spec__0___closed__6:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Array_repr___at___00Std_Async_System_instReprGroupInfo_repr_spec__0___closed__6_value
) as *mut crate::leanh::LeanObject;
pub static l_Array_repr___at___00Std_Async_System_instReprGroupInfo_repr_spec__0___closed__7_value: crate::leanh::LeanStringObject<4> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 4, m_capacity: 4, m_length: 3, m_data: [35, 91, 93, 0]};
static mut l_Array_repr___at___00Std_Async_System_instReprGroupInfo_repr_spec__0___closed__7:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Array_repr___at___00Std_Async_System_instReprGroupInfo_repr_spec__0___closed__7_value
) as *mut crate::leanh::LeanObject;
pub static l_Array_repr___at___00Std_Async_System_instReprGroupInfo_repr_spec__0___closed__8_value: crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 3 }, m_objs: [core::ptr::addr_of!(l_Array_repr___at___00Std_Async_System_instReprGroupInfo_repr_spec__0___closed__7_value) as *mut crate::leanh::LeanObject] };
static mut l_Array_repr___at___00Std_Async_System_instReprGroupInfo_repr_spec__0___closed__8:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Array_repr___at___00Std_Async_System_instReprGroupInfo_repr_spec__0___closed__8_value
) as *mut crate::leanh::LeanObject;
pub static l_Std_Async_System_instReprGroupInfo_repr___redArg___closed__0_value:
    crate::leanh::LeanStringObject<10> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 10,
    m_capacity: 10,
    m_length: 9,
    m_data: [103, 114, 111, 117, 112, 78, 97, 109, 101, 0],
};
static mut l_Std_Async_System_instReprGroupInfo_repr___redArg___closed__0:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Async_System_instReprGroupInfo_repr___redArg___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Async_System_instReprGroupInfo_repr___redArg___closed__1_value:
    crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [core::ptr::addr_of!(
        l_Std_Async_System_instReprGroupInfo_repr___redArg___closed__0_value
    ) as *mut crate::leanh::LeanObject],
};
static mut l_Std_Async_System_instReprGroupInfo_repr___redArg___closed__1:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Async_System_instReprGroupInfo_repr___redArg___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Async_System_instReprGroupInfo_repr___redArg___closed__2_value:
    crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 5,
    },
    m_objs: [
        (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Std_Async_System_instReprGroupInfo_repr___redArg___closed__1_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Std_Async_System_instReprGroupInfo_repr___redArg___closed__2:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Async_System_instReprGroupInfo_repr___redArg___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Async_System_instReprGroupInfo_repr___redArg___closed__3_value:
    crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 5,
    },
    m_objs: [
        core::ptr::addr_of!(l_Std_Async_System_instReprGroupInfo_repr___redArg___closed__2_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Std_Async_System_instReprSystemUser_repr___redArg___closed__5_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Std_Async_System_instReprGroupInfo_repr___redArg___closed__3:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Async_System_instReprGroupInfo_repr___redArg___closed__3_value)
        as *mut crate::leanh::LeanObject;
static mut l_Std_Async_System_instReprGroupInfo_repr___redArg___closed__4_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_Async_System_instReprGroupInfo_repr___redArg___closed__4:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Std_Async_System_instReprGroupInfo_repr___redArg___closed__5_value:
    crate::leanh::LeanStringObject<8> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
static mut l_Std_Async_System_instReprGroupInfo_repr___redArg___closed__5:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Async_System_instReprGroupInfo_repr___redArg___closed__5_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Async_System_instReprGroupInfo_repr___redArg___closed__6_value:
    crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [core::ptr::addr_of!(
        l_Std_Async_System_instReprGroupInfo_repr___redArg___closed__5_value
    ) as *mut crate::leanh::LeanObject],
};
static mut l_Std_Async_System_instReprGroupInfo_repr___redArg___closed__6:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Async_System_instReprGroupInfo_repr___redArg___closed__6_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Async_System_instReprGroupInfo___closed__0_value: crate::leanh::LeanClosureObject<
    0,
> = crate::leanh::LeanClosureObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Std_Async_System_instReprGroupInfo_repr___boxed as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Std_Async_System_instReprGroupInfo___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Async_System_instReprGroupInfo___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Std_Async_System_instReprGroupInfo: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Async_System_instReprGroupInfo___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Async_System_instInhabitedGroupInfo_default___closed__0_value:
    crate::leanh::LeanArrayObject<0> = crate::leanh::LeanArrayObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<usize>() * 2
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 0) as u16,
        other: 0,
        tag: 246,
    },
    m_size: 0,
    m_capacity: 0,
    m_data: [],
};
static mut l_Std_Async_System_instInhabitedGroupInfo_default___closed__0:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Async_System_instInhabitedGroupInfo_default___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Async_System_instInhabitedGroupInfo_default___closed__1_value:
    crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3
            + 0) as u16,
        other: 3,
        tag: 0,
    },
    m_objs: [
        core::ptr::addr_of!(l_Std_Async_System_instInhabitedSystemUser_default___closed__0_value)
            as *mut crate::leanh::LeanObject,
        (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Std_Async_System_instInhabitedGroupInfo_default___closed__0_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Std_Async_System_instInhabitedGroupInfo_default___closed__1:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Async_System_instInhabitedGroupInfo_default___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Std_Async_System_instInhabitedGroupInfo_default: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Async_System_instInhabitedGroupInfo_default___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Std_Async_System_instInhabitedGroupInfo: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Async_System_instInhabitedGroupInfo_default___closed__1_value)
        as *mut crate::leanh::LeanObject;
static mut l_Std_Async_System_instInhabitedCPUTimes_default___closed__0_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_Async_System_instInhabitedCPUTimes_default___closed__0:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static mut l_Std_Async_System_instInhabitedCPUTimes_default: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static mut l_Std_Async_System_instInhabitedCPUTimes: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Std_Async_System_instReprCPUTimes_repr___redArg___closed__0_value:
    crate::leanh::LeanStringObject<9> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
static mut l_Std_Async_System_instReprCPUTimes_repr___redArg___closed__0:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Async_System_instReprCPUTimes_repr___redArg___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Async_System_instReprCPUTimes_repr___redArg___closed__1_value:
    crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [core::ptr::addr_of!(
        l_Std_Async_System_instReprCPUTimes_repr___redArg___closed__0_value
    ) as *mut crate::leanh::LeanObject],
};
static mut l_Std_Async_System_instReprCPUTimes_repr___redArg___closed__1:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Async_System_instReprCPUTimes_repr___redArg___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Async_System_instReprCPUTimes_repr___redArg___closed__2_value:
    crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 5,
    },
    m_objs: [
        (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Std_Async_System_instReprCPUTimes_repr___redArg___closed__1_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Std_Async_System_instReprCPUTimes_repr___redArg___closed__2:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Async_System_instReprCPUTimes_repr___redArg___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Async_System_instReprCPUTimes_repr___redArg___closed__3_value:
    crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 5,
    },
    m_objs: [
        core::ptr::addr_of!(l_Std_Async_System_instReprCPUTimes_repr___redArg___closed__2_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Std_Async_System_instReprSystemUser_repr___redArg___closed__5_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Std_Async_System_instReprCPUTimes_repr___redArg___closed__3:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Async_System_instReprCPUTimes_repr___redArg___closed__3_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Async_System_instReprCPUTimes_repr___redArg___closed__4_value:
    crate::leanh::LeanStringObject<9> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 9,
    m_capacity: 9,
    m_length: 8,
    m_data: [110, 105, 99, 101, 84, 105, 109, 101, 0],
};
static mut l_Std_Async_System_instReprCPUTimes_repr___redArg___closed__4:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Async_System_instReprCPUTimes_repr___redArg___closed__4_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Async_System_instReprCPUTimes_repr___redArg___closed__5_value:
    crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [core::ptr::addr_of!(
        l_Std_Async_System_instReprCPUTimes_repr___redArg___closed__4_value
    ) as *mut crate::leanh::LeanObject],
};
static mut l_Std_Async_System_instReprCPUTimes_repr___redArg___closed__5:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Async_System_instReprCPUTimes_repr___redArg___closed__5_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Async_System_instReprCPUTimes_repr___redArg___closed__6_value:
    crate::leanh::LeanStringObject<11> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
static mut l_Std_Async_System_instReprCPUTimes_repr___redArg___closed__6:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Async_System_instReprCPUTimes_repr___redArg___closed__6_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Async_System_instReprCPUTimes_repr___redArg___closed__7_value:
    crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [core::ptr::addr_of!(
        l_Std_Async_System_instReprCPUTimes_repr___redArg___closed__6_value
    ) as *mut crate::leanh::LeanObject],
};
static mut l_Std_Async_System_instReprCPUTimes_repr___redArg___closed__7:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Async_System_instReprCPUTimes_repr___redArg___closed__7_value)
        as *mut crate::leanh::LeanObject;
static mut l_Std_Async_System_instReprCPUTimes_repr___redArg___closed__8_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_Async_System_instReprCPUTimes_repr___redArg___closed__8:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Std_Async_System_instReprCPUTimes_repr___redArg___closed__9_value:
    crate::leanh::LeanStringObject<9> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 9,
    m_capacity: 9,
    m_length: 8,
    m_data: [105, 100, 108, 101, 84, 105, 109, 101, 0],
};
static mut l_Std_Async_System_instReprCPUTimes_repr___redArg___closed__9:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Async_System_instReprCPUTimes_repr___redArg___closed__9_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Async_System_instReprCPUTimes_repr___redArg___closed__10_value:
    crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [core::ptr::addr_of!(
        l_Std_Async_System_instReprCPUTimes_repr___redArg___closed__9_value
    ) as *mut crate::leanh::LeanObject],
};
static mut l_Std_Async_System_instReprCPUTimes_repr___redArg___closed__10:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Async_System_instReprCPUTimes_repr___redArg___closed__10_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Async_System_instReprCPUTimes_repr___redArg___closed__11_value:
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
        105, 110, 116, 101, 114, 114, 117, 112, 116, 84, 105, 109, 101, 0,
    ],
};
static mut l_Std_Async_System_instReprCPUTimes_repr___redArg___closed__11:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Async_System_instReprCPUTimes_repr___redArg___closed__11_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Async_System_instReprCPUTimes_repr___redArg___closed__12_value:
    crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [core::ptr::addr_of!(
        l_Std_Async_System_instReprCPUTimes_repr___redArg___closed__11_value
    ) as *mut crate::leanh::LeanObject],
};
static mut l_Std_Async_System_instReprCPUTimes_repr___redArg___closed__12:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Async_System_instReprCPUTimes_repr___redArg___closed__12_value)
        as *mut crate::leanh::LeanObject;
static mut l_Std_Async_System_instReprCPUTimes_repr___redArg___closed__13_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_Async_System_instReprCPUTimes_repr___redArg___closed__13:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Std_Async_System_instReprCPUTimes___closed__0_value: crate::leanh::LeanClosureObject<
    0,
> = crate::leanh::LeanClosureObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Std_Async_System_instReprCPUTimes_repr___boxed as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Std_Async_System_instReprCPUTimes___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Async_System_instReprCPUTimes___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Std_Async_System_instReprCPUTimes: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Async_System_instReprCPUTimes___closed__0_value)
        as *mut crate::leanh::LeanObject;
static mut l_Std_Async_System_instInhabitedCPUInfo_default___closed__0_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_Async_System_instInhabitedCPUInfo_default___closed__0:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static mut l_Std_Async_System_instInhabitedCPUInfo_default: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static mut l_Std_Async_System_instInhabitedCPUInfo: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Std_Async_System_instReprCPUInfo_repr___redArg___closed__0_value:
    crate::leanh::LeanStringObject<6> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
static mut l_Std_Async_System_instReprCPUInfo_repr___redArg___closed__0:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Async_System_instReprCPUInfo_repr___redArg___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Async_System_instReprCPUInfo_repr___redArg___closed__1_value:
    crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [
        core::ptr::addr_of!(l_Std_Async_System_instReprCPUInfo_repr___redArg___closed__0_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Std_Async_System_instReprCPUInfo_repr___redArg___closed__1:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Async_System_instReprCPUInfo_repr___redArg___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Async_System_instReprCPUInfo_repr___redArg___closed__2_value:
    crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 5,
    },
    m_objs: [
        (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Std_Async_System_instReprCPUInfo_repr___redArg___closed__1_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Std_Async_System_instReprCPUInfo_repr___redArg___closed__2:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Async_System_instReprCPUInfo_repr___redArg___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Async_System_instReprCPUInfo_repr___redArg___closed__3_value:
    crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 5,
    },
    m_objs: [
        core::ptr::addr_of!(l_Std_Async_System_instReprCPUInfo_repr___redArg___closed__2_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Std_Async_System_instReprSystemUser_repr___redArg___closed__5_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Std_Async_System_instReprCPUInfo_repr___redArg___closed__3:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Async_System_instReprCPUInfo_repr___redArg___closed__3_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Async_System_instReprCPUInfo_repr___redArg___closed__4_value:
    crate::leanh::LeanStringObject<6> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
static mut l_Std_Async_System_instReprCPUInfo_repr___redArg___closed__4:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Async_System_instReprCPUInfo_repr___redArg___closed__4_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Async_System_instReprCPUInfo_repr___redArg___closed__5_value:
    crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [
        core::ptr::addr_of!(l_Std_Async_System_instReprCPUInfo_repr___redArg___closed__4_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Std_Async_System_instReprCPUInfo_repr___redArg___closed__5:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Async_System_instReprCPUInfo_repr___redArg___closed__5_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Async_System_instReprCPUInfo_repr___redArg___closed__6_value:
    crate::leanh::LeanStringObject<6> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
static mut l_Std_Async_System_instReprCPUInfo_repr___redArg___closed__6:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Async_System_instReprCPUInfo_repr___redArg___closed__6_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Async_System_instReprCPUInfo_repr___redArg___closed__7_value:
    crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [
        core::ptr::addr_of!(l_Std_Async_System_instReprCPUInfo_repr___redArg___closed__6_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Std_Async_System_instReprCPUInfo_repr___redArg___closed__7:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Async_System_instReprCPUInfo_repr___redArg___closed__7_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Async_System_instReprCPUInfo___closed__0_value: crate::leanh::LeanClosureObject<
    0,
> = crate::leanh::LeanClosureObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Std_Async_System_instReprCPUInfo_repr___boxed as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Std_Async_System_instReprCPUInfo___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Async_System_instReprCPUInfo___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Std_Async_System_instReprCPUInfo: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Async_System_instReprCPUInfo___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Async_System_instReprOSInfo_repr___redArg___closed__0_value:
    crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 5,
    m_capacity: 5,
    m_length: 4,
    m_data: [110, 97, 109, 101, 0],
};
static mut l_Std_Async_System_instReprOSInfo_repr___redArg___closed__0:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Async_System_instReprOSInfo_repr___redArg___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Async_System_instReprOSInfo_repr___redArg___closed__1_value:
    crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [
        core::ptr::addr_of!(l_Std_Async_System_instReprOSInfo_repr___redArg___closed__0_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Std_Async_System_instReprOSInfo_repr___redArg___closed__1:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Async_System_instReprOSInfo_repr___redArg___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Async_System_instReprOSInfo_repr___redArg___closed__2_value:
    crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 5,
    },
    m_objs: [
        (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Std_Async_System_instReprOSInfo_repr___redArg___closed__1_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Std_Async_System_instReprOSInfo_repr___redArg___closed__2:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Async_System_instReprOSInfo_repr___redArg___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Async_System_instReprOSInfo_repr___redArg___closed__3_value:
    crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 5,
    },
    m_objs: [
        core::ptr::addr_of!(l_Std_Async_System_instReprOSInfo_repr___redArg___closed__2_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Std_Async_System_instReprSystemUser_repr___redArg___closed__5_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Std_Async_System_instReprOSInfo_repr___redArg___closed__3:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Async_System_instReprOSInfo_repr___redArg___closed__3_value)
        as *mut crate::leanh::LeanObject;
static mut l_Std_Async_System_instReprOSInfo_repr___redArg___closed__4_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_Async_System_instReprOSInfo_repr___redArg___closed__4:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Std_Async_System_instReprOSInfo_repr___redArg___closed__5_value:
    crate::leanh::LeanStringObject<8> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
static mut l_Std_Async_System_instReprOSInfo_repr___redArg___closed__5:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Async_System_instReprOSInfo_repr___redArg___closed__5_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Async_System_instReprOSInfo_repr___redArg___closed__6_value:
    crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [
        core::ptr::addr_of!(l_Std_Async_System_instReprOSInfo_repr___redArg___closed__5_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Std_Async_System_instReprOSInfo_repr___redArg___closed__6:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Async_System_instReprOSInfo_repr___redArg___closed__6_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Async_System_instReprOSInfo_repr___redArg___closed__7_value:
    crate::leanh::LeanStringObject<8> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
static mut l_Std_Async_System_instReprOSInfo_repr___redArg___closed__7:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Async_System_instReprOSInfo_repr___redArg___closed__7_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Async_System_instReprOSInfo_repr___redArg___closed__8_value:
    crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [
        core::ptr::addr_of!(l_Std_Async_System_instReprOSInfo_repr___redArg___closed__7_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Std_Async_System_instReprOSInfo_repr___redArg___closed__8:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Async_System_instReprOSInfo_repr___redArg___closed__8_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Async_System_instReprOSInfo_repr___redArg___closed__9_value:
    crate::leanh::LeanStringObject<8> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
static mut l_Std_Async_System_instReprOSInfo_repr___redArg___closed__9:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Async_System_instReprOSInfo_repr___redArg___closed__9_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Async_System_instReprOSInfo_repr___redArg___closed__10_value:
    crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [
        core::ptr::addr_of!(l_Std_Async_System_instReprOSInfo_repr___redArg___closed__9_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Std_Async_System_instReprOSInfo_repr___redArg___closed__10:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Async_System_instReprOSInfo_repr___redArg___closed__10_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Async_System_instReprOSInfo___closed__0_value: crate::leanh::LeanClosureObject<0> =
    crate::leanh::LeanClosureObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 0)
                as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Std_Async_System_instReprOSInfo_repr___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Std_Async_System_instReprOSInfo___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Async_System_instReprOSInfo___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Std_Async_System_instReprOSInfo: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Async_System_instReprOSInfo___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Async_System_instInhabitedOSInfo_default___closed__0_value:
    crate::leanh::LeanCtorObject<4> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 4
            + 0) as u16,
        other: 4,
        tag: 0,
    },
    m_objs: [
        core::ptr::addr_of!(l_Std_Async_System_instInhabitedSystemUser_default___closed__0_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Std_Async_System_instInhabitedSystemUser_default___closed__0_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Std_Async_System_instInhabitedSystemUser_default___closed__0_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Std_Async_System_instInhabitedSystemUser_default___closed__0_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Std_Async_System_instInhabitedOSInfo_default___closed__0:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Async_System_instInhabitedOSInfo_default___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Std_Async_System_instInhabitedOSInfo_default: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Async_System_instInhabitedOSInfo_default___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Std_Async_System_instInhabitedOSInfo: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Async_System_instInhabitedOSInfo_default___closed__0_value)
        as *mut crate::leanh::LeanObject;
static mut l_Std_Async_System_instInhabitedEnvironment_default___closed__0_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_Async_System_instInhabitedEnvironment_default___closed__0:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Std_Async_System_instInhabitedEnvironment_default___closed__1_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_Async_System_instInhabitedEnvironment_default___closed__1:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static mut l_Std_Async_System_instInhabitedEnvironment_default: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static mut l_Std_Async_System_instInhabitedEnvironment: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Prod_repr___at___00List_repr___at___00Std_Async_System_instReprEnvironment_repr_spec__0_spec__0___redArg___closed__0_value: crate::leanh::LeanStringObject<2> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [40, 0]};
static mut l_Prod_repr___at___00List_repr___at___00Std_Async_System_instReprEnvironment_repr_spec__0_spec__0___redArg___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Prod_repr___at___00List_repr___at___00Std_Async_System_instReprEnvironment_repr_spec__0_spec__0___redArg___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_Prod_repr___at___00List_repr___at___00Std_Async_System_instReprEnvironment_repr_spec__0_spec__0___redArg___closed__1_value: crate::leanh::LeanStringObject<2> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [41, 0]};
static mut l_Prod_repr___at___00List_repr___at___00Std_Async_System_instReprEnvironment_repr_spec__0_spec__0___redArg___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Prod_repr___at___00List_repr___at___00Std_Async_System_instReprEnvironment_repr_spec__0_spec__0___redArg___closed__1_value) as *mut crate::leanh::LeanObject;
static mut l_Prod_repr___at___00List_repr___at___00Std_Async_System_instReprEnvironment_repr_spec__0_spec__0___redArg___closed__2_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Prod_repr___at___00List_repr___at___00Std_Async_System_instReprEnvironment_repr_spec__0_spec__0___redArg___closed__2: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Prod_repr___at___00List_repr___at___00Std_Async_System_instReprEnvironment_repr_spec__0_spec__0___redArg___closed__3_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Prod_repr___at___00List_repr___at___00Std_Async_System_instReprEnvironment_repr_spec__0_spec__0___redArg___closed__3: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Prod_repr___at___00List_repr___at___00Std_Async_System_instReprEnvironment_repr_spec__0_spec__0___redArg___closed__4_value: crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 3 }, m_objs: [core::ptr::addr_of!(l_Prod_repr___at___00List_repr___at___00Std_Async_System_instReprEnvironment_repr_spec__0_spec__0___redArg___closed__0_value) as *mut crate::leanh::LeanObject] };
static mut l_Prod_repr___at___00List_repr___at___00Std_Async_System_instReprEnvironment_repr_spec__0_spec__0___redArg___closed__4: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Prod_repr___at___00List_repr___at___00Std_Async_System_instReprEnvironment_repr_spec__0_spec__0___redArg___closed__4_value) as *mut crate::leanh::LeanObject;
pub static l_Prod_repr___at___00List_repr___at___00Std_Async_System_instReprEnvironment_repr_spec__0_spec__0___redArg___closed__5_value: crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 3 }, m_objs: [core::ptr::addr_of!(l_Prod_repr___at___00List_repr___at___00Std_Async_System_instReprEnvironment_repr_spec__0_spec__0___redArg___closed__1_value) as *mut crate::leanh::LeanObject] };
static mut l_Prod_repr___at___00List_repr___at___00Std_Async_System_instReprEnvironment_repr_spec__0_spec__0___redArg___closed__5: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Prod_repr___at___00List_repr___at___00Std_Async_System_instReprEnvironment_repr_spec__0_spec__0___redArg___closed__5_value) as *mut crate::leanh::LeanObject;
pub static l_List_repr___at___00Std_Async_System_instReprEnvironment_repr_spec__0___redArg___closed__0_value: crate::leanh::LeanStringObject<3> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 3, m_capacity: 3, m_length: 2, m_data: [91, 93, 0]};
static mut l_List_repr___at___00Std_Async_System_instReprEnvironment_repr_spec__0___redArg___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_List_repr___at___00Std_Async_System_instReprEnvironment_repr_spec__0___redArg___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_List_repr___at___00Std_Async_System_instReprEnvironment_repr_spec__0___redArg___closed__1_value: crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 3 }, m_objs: [core::ptr::addr_of!(l_List_repr___at___00Std_Async_System_instReprEnvironment_repr_spec__0___redArg___closed__0_value) as *mut crate::leanh::LeanObject] };
static mut l_List_repr___at___00Std_Async_System_instReprEnvironment_repr_spec__0___redArg___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_List_repr___at___00Std_Async_System_instReprEnvironment_repr_spec__0___redArg___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l_List_repr___at___00Std_Async_System_instReprEnvironment_repr_spec__0___redArg___closed__2_value: crate::leanh::LeanStringObject<2> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [91, 0]};
static mut l_List_repr___at___00Std_Async_System_instReprEnvironment_repr_spec__0___redArg___closed__2: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_List_repr___at___00Std_Async_System_instReprEnvironment_repr_spec__0___redArg___closed__2_value) as *mut crate::leanh::LeanObject;
static mut l_List_repr___at___00Std_Async_System_instReprEnvironment_repr_spec__0___redArg___closed__3_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_List_repr___at___00Std_Async_System_instReprEnvironment_repr_spec__0___redArg___closed__3: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_List_repr___at___00Std_Async_System_instReprEnvironment_repr_spec__0___redArg___closed__4_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_List_repr___at___00Std_Async_System_instReprEnvironment_repr_spec__0___redArg___closed__4: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_List_repr___at___00Std_Async_System_instReprEnvironment_repr_spec__0___redArg___closed__5_value: crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 3 }, m_objs: [core::ptr::addr_of!(l_List_repr___at___00Std_Async_System_instReprEnvironment_repr_spec__0___redArg___closed__2_value) as *mut crate::leanh::LeanObject] };
static mut l_List_repr___at___00Std_Async_System_instReprEnvironment_repr_spec__0___redArg___closed__5: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_List_repr___at___00Std_Async_System_instReprEnvironment_repr_spec__0___redArg___closed__5_value) as *mut crate::leanh::LeanObject;
pub static l_Std_Async_System_instReprEnvironment_repr___redArg___closed__0_value:
    crate::leanh::LeanStringObject<10> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 10,
    m_capacity: 10,
    m_length: 9,
    m_data: [116, 111, 72, 97, 115, 104, 77, 97, 112, 0],
};
static mut l_Std_Async_System_instReprEnvironment_repr___redArg___closed__0:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Async_System_instReprEnvironment_repr___redArg___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Async_System_instReprEnvironment_repr___redArg___closed__1_value:
    crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [core::ptr::addr_of!(
        l_Std_Async_System_instReprEnvironment_repr___redArg___closed__0_value
    ) as *mut crate::leanh::LeanObject],
};
static mut l_Std_Async_System_instReprEnvironment_repr___redArg___closed__1:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Async_System_instReprEnvironment_repr___redArg___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Async_System_instReprEnvironment_repr___redArg___closed__2_value:
    crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 5,
    },
    m_objs: [
        (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Std_Async_System_instReprEnvironment_repr___redArg___closed__1_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Std_Async_System_instReprEnvironment_repr___redArg___closed__2:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Async_System_instReprEnvironment_repr___redArg___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Async_System_instReprEnvironment_repr___redArg___closed__3_value:
    crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 5,
    },
    m_objs: [
        core::ptr::addr_of!(l_Std_Async_System_instReprEnvironment_repr___redArg___closed__2_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Std_Async_System_instReprSystemUser_repr___redArg___closed__5_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Std_Async_System_instReprEnvironment_repr___redArg___closed__3:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Async_System_instReprEnvironment_repr___redArg___closed__3_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Async_System_instReprEnvironment_repr___redArg___closed__4_value:
    crate::leanh::LeanStringObject<20> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 20,
    m_capacity: 20,
    m_length: 19,
    m_data: [
        83, 116, 100, 46, 72, 97, 115, 104, 77, 97, 112, 46, 111, 102, 76, 105, 115, 116, 32, 0,
    ],
};
static mut l_Std_Async_System_instReprEnvironment_repr___redArg___closed__4:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Async_System_instReprEnvironment_repr___redArg___closed__4_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Async_System_instReprEnvironment_repr___redArg___closed__5_value:
    crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [core::ptr::addr_of!(
        l_Std_Async_System_instReprEnvironment_repr___redArg___closed__4_value
    ) as *mut crate::leanh::LeanObject],
};
static mut l_Std_Async_System_instReprEnvironment_repr___redArg___closed__5:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Async_System_instReprEnvironment_repr___redArg___closed__5_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Async_System_instReprEnvironment___closed__0_value:
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
    m_fun: l_Std_Async_System_instReprEnvironment_repr___boxed as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Std_Async_System_instReprEnvironment___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Async_System_instReprEnvironment___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Std_Async_System_instReprEnvironment: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Async_System_instReprEnvironment___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Async_System_Environment_get_x3f___closed__0_value:
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
    m_fun: l_String_hash___boxed as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Std_Async_System_Environment_get_x3f___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Async_System_Environment_get_x3f___closed__0_value)
        as *mut crate::leanh::LeanObject;
static mut l_Std_Async_System_Environment_get_x3f___closed__1_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Async_System_Environment_get_x3f___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Std_Async_System_getEnv___closed__0_value: crate::leanh::LeanClosureObject<0> =
    crate::leanh::LeanClosureObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 0)
                as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Id_instMonad___lam__0 as *const core::ffi::c_void,
        m_arity: 4,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Std_Async_System_getEnv___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Async_System_getEnv___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Async_System_getEnv___closed__1_value: crate::leanh::LeanClosureObject<0> =
    crate::leanh::LeanClosureObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 0)
                as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Id_instMonad___lam__1___boxed as *const core::ffi::c_void,
        m_arity: 4,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Std_Async_System_getEnv___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Async_System_getEnv___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Async_System_getEnv___closed__2_value: crate::leanh::LeanClosureObject<0> =
    crate::leanh::LeanClosureObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 0)
                as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Id_instMonad___lam__2___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Std_Async_System_getEnv___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Async_System_getEnv___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Async_System_getEnv___closed__3_value: crate::leanh::LeanClosureObject<0> =
    crate::leanh::LeanClosureObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 0)
                as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Id_instMonad___lam__3 as *const core::ffi::c_void,
        m_arity: 4,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Std_Async_System_getEnv___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Async_System_getEnv___closed__3_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Async_System_getEnv___closed__4_value: crate::leanh::LeanClosureObject<0> =
    crate::leanh::LeanClosureObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 0)
                as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Id_instMonad___lam__4___boxed as *const core::ffi::c_void,
        m_arity: 4,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Std_Async_System_getEnv___closed__4: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Async_System_getEnv___closed__4_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Async_System_getEnv___closed__5_value: crate::leanh::LeanClosureObject<0> =
    crate::leanh::LeanClosureObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 0)
                as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Id_instMonad___lam__5___boxed as *const core::ffi::c_void,
        m_arity: 4,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Std_Async_System_getEnv___closed__5: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Async_System_getEnv___closed__5_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Async_System_getEnv___closed__6_value: crate::leanh::LeanClosureObject<0> =
    crate::leanh::LeanClosureObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 0)
                as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Id_instMonad___lam__6 as *const core::ffi::c_void,
        m_arity: 4,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Std_Async_System_getEnv___closed__6: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Async_System_getEnv___closed__6_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Async_System_getEnv___closed__7_value: crate::leanh::LeanCtorObject<2> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
                + 0) as u16,
            other: 2,
            tag: 0,
        },
        m_objs: [
            core::ptr::addr_of!(l_Std_Async_System_getEnv___closed__0_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Std_Async_System_getEnv___closed__1_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Std_Async_System_getEnv___closed__7: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Async_System_getEnv___closed__7_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Async_System_getEnv___closed__8_value: crate::leanh::LeanCtorObject<5> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 5
                + 0) as u16,
            other: 5,
            tag: 0,
        },
        m_objs: [
            core::ptr::addr_of!(l_Std_Async_System_getEnv___closed__7_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Std_Async_System_getEnv___closed__2_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Std_Async_System_getEnv___closed__3_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Std_Async_System_getEnv___closed__4_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Std_Async_System_getEnv___closed__5_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Std_Async_System_getEnv___closed__8: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Async_System_getEnv___closed__8_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Async_System_getEnv___closed__9_value: crate::leanh::LeanCtorObject<2> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
                + 0) as u16,
            other: 2,
            tag: 0,
        },
        m_objs: [
            core::ptr::addr_of!(l_Std_Async_System_getEnv___closed__8_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Std_Async_System_getEnv___closed__6_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Std_Async_System_getEnv___closed__9: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Async_System_getEnv___closed__9_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Async_System_getEnv___closed__10_value: crate::leanh::LeanClosureObject<1> =
    crate::leanh::LeanClosureObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1)
                as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Array_instForIn_x27InferInstanceMembershipOfMonad___redArg___lam__0
            as *const core::ffi::c_void,
        m_arity: 5,
        m_num_fixed: 1,
        m_objs: [
            core::ptr::addr_of!(l_Std_Async_System_getEnv___closed__9_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Std_Async_System_getEnv___closed__10: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Async_System_getEnv___closed__10_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Async_System_getEnv___closed__11_value: crate::leanh::LeanClosureObject<1> =
    crate::leanh::LeanClosureObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1)
                as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_instForInOfForIn_x27___redArg___lam__1 as *const core::ffi::c_void,
        m_arity: 5,
        m_num_fixed: 1,
        m_objs: [
            core::ptr::addr_of!(l_Std_Async_System_getEnv___closed__10_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Std_Async_System_getEnv___closed__11: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Async_System_getEnv___closed__11_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Async_System_getGroup___closed__0_value: crate::leanh::LeanClosureObject<0> =
    crate::leanh::LeanClosureObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 0)
                as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Std_Async_System_getGroup___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Std_Async_System_getGroup___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Async_System_getGroup___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub unsafe fn _init_l_Std_Async_System_instInhabitedGroupId_default()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1453_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1453_ = crate::leanh::lean_unsigned_to_nat(0);
    return v___x_1453_;
}
pub unsafe fn _init_l_Std_Async_System_instInhabitedGroupId() -> *mut crate::leanh::LeanObject {
    let mut v___x_1454_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1454_ = crate::leanh::lean_unsigned_to_nat(0);
    return v___x_1454_;
}
pub unsafe fn l_Std_Async_System_instDecidableEqGroupId_decEq(
    mut v_x_1455_: *mut crate::leanh::LeanObject,
    mut v_x_1456_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_1457_: u8 = 0;
    v___x_1457_ = lean_nat_dec_eq(v_x_1455_, v_x_1456_);
    return v___x_1457_;
}
pub unsafe fn l_Std_Async_System_instDecidableEqGroupId_decEq___boxed(
    mut v_x_1458_: *mut crate::leanh::LeanObject,
    mut v_x_1459_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1460_: u8 = 0;
    let mut v_r_1461_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1460_ = l_Std_Async_System_instDecidableEqGroupId_decEq(v_x_1458_, v_x_1459_);
    crate::leanh::lean_dec(v_x_1459_);
    crate::leanh::lean_dec(v_x_1458_);
    v_r_1461_ = crate::leanh::lean_box((v_res_1460_) as usize);
    return v_r_1461_;
}
pub unsafe fn l_Std_Async_System_instDecidableEqGroupId(
    mut v_x_1462_: *mut crate::leanh::LeanObject,
    mut v_x_1463_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_1464_: u8 = 0;
    v___x_1464_ = lean_nat_dec_eq(v_x_1462_, v_x_1463_);
    return v___x_1464_;
}
pub unsafe fn l_Std_Async_System_instDecidableEqGroupId___boxed(
    mut v_x_1465_: *mut crate::leanh::LeanObject,
    mut v_x_1466_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1467_: u8 = 0;
    let mut v_r_1468_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1467_ = l_Std_Async_System_instDecidableEqGroupId(v_x_1465_, v_x_1466_);
    crate::leanh::lean_dec(v_x_1466_);
    crate::leanh::lean_dec(v_x_1465_);
    v_r_1468_ = crate::leanh::lean_box((v_res_1467_) as usize);
    return v_r_1468_;
}
pub unsafe fn l_Std_Async_System_instOrdGroupId_ord(
    mut v_x_1469_: *mut crate::leanh::LeanObject,
    mut v_x_1470_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_1471_: u8 = 0;
    v___x_1471_ = lean_nat_dec_lt(v_x_1469_, v_x_1470_);
    if v___x_1471_ == 0 {
        let mut v___x_1472_: u8 = 0;
        v___x_1472_ = lean_nat_dec_eq(v_x_1469_, v_x_1470_);
        if v___x_1472_ == 0 {
            let mut v___x_1473_: u8 = 0;
            v___x_1473_ = 2;
            return v___x_1473_;
        } else {
            let mut v___x_1474_: u8 = 0;
            v___x_1474_ = 1;
            return v___x_1474_;
        }
    } else {
        let mut v___x_1475_: u8 = 0;
        v___x_1475_ = 0;
        return v___x_1475_;
    }
}
pub unsafe fn l_Std_Async_System_instOrdGroupId_ord___boxed(
    mut v_x_1476_: *mut crate::leanh::LeanObject,
    mut v_x_1477_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1478_: u8 = 0;
    let mut v_r_1479_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1478_ = l_Std_Async_System_instOrdGroupId_ord(v_x_1476_, v_x_1477_);
    crate::leanh::lean_dec(v_x_1477_);
    crate::leanh::lean_dec(v_x_1476_);
    v_r_1479_ = crate::leanh::lean_box((v_res_1478_) as usize);
    return v_r_1479_;
}
pub unsafe fn l_Std_Async_System_instReprGroupId___lam__0(
    mut v_g_1485_: *mut crate::leanh::LeanObject,
    mut v___y_1486_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1487_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1488_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1489_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1490_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1491_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1487_ = l_Std_Async_System_instReprGroupId___lam__0___closed__1;
    v___x_1488_ = l_Nat_reprFast(v_g_1485_);
    v___x_1489_ = crate::leanh::lean_alloc_ctor(3, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1489_, 0, v___x_1488_);
    v___x_1490_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1490_, 0, v___x_1487_);
    crate::leanh::lean_ctor_set(v___x_1490_, 1, v___x_1489_);
    v___x_1491_ = l_Repr_addAppParen(v___x_1490_, v___y_1486_);
    return v___x_1491_;
}
pub unsafe fn l_Std_Async_System_instReprGroupId___lam__0___boxed(
    mut v_g_1492_: *mut crate::leanh::LeanObject,
    mut v___y_1493_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1494_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1494_ = l_Std_Async_System_instReprGroupId___lam__0(v_g_1492_, v___y_1493_);
    crate::leanh::lean_dec(v___y_1493_);
    return v_res_1494_;
}
pub unsafe fn _init_l_Std_Async_System_instInhabitedUserId_default() -> *mut crate::leanh::LeanObject
{
    let mut v___x_1497_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1497_ = crate::leanh::lean_unsigned_to_nat(0);
    return v___x_1497_;
}
pub unsafe fn _init_l_Std_Async_System_instInhabitedUserId() -> *mut crate::leanh::LeanObject {
    let mut v___x_1498_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1498_ = crate::leanh::lean_unsigned_to_nat(0);
    return v___x_1498_;
}
pub unsafe fn l_Std_Async_System_instDecidableEqUserId_decEq(
    mut v_x_1499_: *mut crate::leanh::LeanObject,
    mut v_x_1500_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_1501_: u8 = 0;
    v___x_1501_ = lean_nat_dec_eq(v_x_1499_, v_x_1500_);
    return v___x_1501_;
}
pub unsafe fn l_Std_Async_System_instDecidableEqUserId_decEq___boxed(
    mut v_x_1502_: *mut crate::leanh::LeanObject,
    mut v_x_1503_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1504_: u8 = 0;
    let mut v_r_1505_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1504_ = l_Std_Async_System_instDecidableEqUserId_decEq(v_x_1502_, v_x_1503_);
    crate::leanh::lean_dec(v_x_1503_);
    crate::leanh::lean_dec(v_x_1502_);
    v_r_1505_ = crate::leanh::lean_box((v_res_1504_) as usize);
    return v_r_1505_;
}
pub unsafe fn l_Std_Async_System_instDecidableEqUserId(
    mut v_x_1506_: *mut crate::leanh::LeanObject,
    mut v_x_1507_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_1508_: u8 = 0;
    v___x_1508_ = lean_nat_dec_eq(v_x_1506_, v_x_1507_);
    return v___x_1508_;
}
pub unsafe fn l_Std_Async_System_instDecidableEqUserId___boxed(
    mut v_x_1509_: *mut crate::leanh::LeanObject,
    mut v_x_1510_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1511_: u8 = 0;
    let mut v_r_1512_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1511_ = l_Std_Async_System_instDecidableEqUserId(v_x_1509_, v_x_1510_);
    crate::leanh::lean_dec(v_x_1510_);
    crate::leanh::lean_dec(v_x_1509_);
    v_r_1512_ = crate::leanh::lean_box((v_res_1511_) as usize);
    return v_r_1512_;
}
pub unsafe fn l_Std_Async_System_instOrdUserId_ord(
    mut v_x_1513_: *mut crate::leanh::LeanObject,
    mut v_x_1514_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_1515_: u8 = 0;
    v___x_1515_ = lean_nat_dec_lt(v_x_1513_, v_x_1514_);
    if v___x_1515_ == 0 {
        let mut v___x_1516_: u8 = 0;
        v___x_1516_ = lean_nat_dec_eq(v_x_1513_, v_x_1514_);
        if v___x_1516_ == 0 {
            let mut v___x_1517_: u8 = 0;
            v___x_1517_ = 2;
            return v___x_1517_;
        } else {
            let mut v___x_1518_: u8 = 0;
            v___x_1518_ = 1;
            return v___x_1518_;
        }
    } else {
        let mut v___x_1519_: u8 = 0;
        v___x_1519_ = 0;
        return v___x_1519_;
    }
}
pub unsafe fn l_Std_Async_System_instOrdUserId_ord___boxed(
    mut v_x_1520_: *mut crate::leanh::LeanObject,
    mut v_x_1521_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1522_: u8 = 0;
    let mut v_r_1523_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1522_ = l_Std_Async_System_instOrdUserId_ord(v_x_1520_, v_x_1521_);
    crate::leanh::lean_dec(v_x_1521_);
    crate::leanh::lean_dec(v_x_1520_);
    v_r_1523_ = crate::leanh::lean_box((v_res_1522_) as usize);
    return v_r_1523_;
}
pub unsafe fn l_Std_Async_System_instReprUserId___lam__0(
    mut v_u_1529_: *mut crate::leanh::LeanObject,
    mut v___y_1530_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1531_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1532_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1533_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1534_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1535_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1531_ = l_Std_Async_System_instReprUserId___lam__0___closed__1;
    v___x_1532_ = l_Nat_reprFast(v_u_1529_);
    v___x_1533_ = crate::leanh::lean_alloc_ctor(3, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1533_, 0, v___x_1532_);
    v___x_1534_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1534_, 0, v___x_1531_);
    crate::leanh::lean_ctor_set(v___x_1534_, 1, v___x_1533_);
    v___x_1535_ = l_Repr_addAppParen(v___x_1534_, v___y_1530_);
    return v___x_1535_;
}
pub unsafe fn l_Std_Async_System_instReprUserId___lam__0___boxed(
    mut v_u_1536_: *mut crate::leanh::LeanObject,
    mut v___y_1537_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1538_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1538_ = l_Std_Async_System_instReprUserId___lam__0(v_u_1536_, v___y_1537_);
    crate::leanh::lean_dec(v___y_1537_);
    return v_res_1538_;
}
pub unsafe fn l_Std_Async_System_instDecidableEqSystemUser_decEq(
    mut v_x_1547_: *mut crate::leanh::LeanObject,
    mut v_x_1548_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v_username_1549_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_userId_1550_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_groupId_1551_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_shell_1552_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_homeDir_1553_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_username_1554_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_userId_1555_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_groupId_1556_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_shell_1557_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_homeDir_1558_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1559_: u8 = 0;
    v_username_1549_ = crate::leanh::lean_ctor_get(v_x_1547_, 0);
    crate::leanh::lean_inc_ref(v_username_1549_);
    v_userId_1550_ = crate::leanh::lean_ctor_get(v_x_1547_, 1);
    crate::leanh::lean_inc(v_userId_1550_);
    v_groupId_1551_ = crate::leanh::lean_ctor_get(v_x_1547_, 2);
    crate::leanh::lean_inc(v_groupId_1551_);
    v_shell_1552_ = crate::leanh::lean_ctor_get(v_x_1547_, 3);
    crate::leanh::lean_inc(v_shell_1552_);
    v_homeDir_1553_ = crate::leanh::lean_ctor_get(v_x_1547_, 4);
    crate::leanh::lean_inc(v_homeDir_1553_);
    crate::leanh::lean_dec_ref(v_x_1547_);
    v_username_1554_ = crate::leanh::lean_ctor_get(v_x_1548_, 0);
    crate::leanh::lean_inc_ref(v_username_1554_);
    v_userId_1555_ = crate::leanh::lean_ctor_get(v_x_1548_, 1);
    crate::leanh::lean_inc(v_userId_1555_);
    v_groupId_1556_ = crate::leanh::lean_ctor_get(v_x_1548_, 2);
    crate::leanh::lean_inc(v_groupId_1556_);
    v_shell_1557_ = crate::leanh::lean_ctor_get(v_x_1548_, 3);
    crate::leanh::lean_inc(v_shell_1557_);
    v_homeDir_1558_ = crate::leanh::lean_ctor_get(v_x_1548_, 4);
    crate::leanh::lean_inc(v_homeDir_1558_);
    crate::leanh::lean_dec_ref(v_x_1548_);
    v___x_1559_ = lean_string_dec_eq(v_username_1549_, v_username_1554_);
    crate::leanh::lean_dec_ref(v_username_1554_);
    crate::leanh::lean_dec_ref(v_username_1549_);
    if v___x_1559_ == 0 {
        crate::leanh::lean_dec(v_homeDir_1558_);
        crate::leanh::lean_dec(v_shell_1557_);
        crate::leanh::lean_dec(v_groupId_1556_);
        crate::leanh::lean_dec(v_userId_1555_);
        crate::leanh::lean_dec(v_homeDir_1553_);
        crate::leanh::lean_dec(v_shell_1552_);
        crate::leanh::lean_dec(v_groupId_1551_);
        crate::leanh::lean_dec(v_userId_1550_);
        return v___x_1559_;
    } else {
        let mut v___x_1560_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1561_: u8 = 0;
        v___x_1560_ = crate::leanh::lean_alloc_closure(
            l_Std_Async_System_instDecidableEqUserId___boxed as *mut core::ffi::c_void,
            2,
            0,
        );
        v___x_1561_ =
            l_Option_instDecidableEq___redArg(v___x_1560_, v_userId_1550_, v_userId_1555_);
        if v___x_1561_ == 0 {
            crate::leanh::lean_dec(v_homeDir_1558_);
            crate::leanh::lean_dec(v_shell_1557_);
            crate::leanh::lean_dec(v_groupId_1556_);
            crate::leanh::lean_dec(v_homeDir_1553_);
            crate::leanh::lean_dec(v_shell_1552_);
            crate::leanh::lean_dec(v_groupId_1551_);
            return v___x_1561_;
        } else {
            let mut v___x_1562_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1563_: u8 = 0;
            v___x_1562_ = crate::leanh::lean_alloc_closure(
                l_Std_Async_System_instDecidableEqGroupId___boxed as *mut core::ffi::c_void,
                2,
                0,
            );
            v___x_1563_ =
                l_Option_instDecidableEq___redArg(v___x_1562_, v_groupId_1551_, v_groupId_1556_);
            if v___x_1563_ == 0 {
                crate::leanh::lean_dec(v_homeDir_1558_);
                crate::leanh::lean_dec(v_shell_1557_);
                crate::leanh::lean_dec(v_homeDir_1553_);
                crate::leanh::lean_dec(v_shell_1552_);
                return v___x_1563_;
            } else {
                let mut v___x_1564_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_1565_: u8 = 0;
                v___x_1564_ = crate::leanh::lean_alloc_closure(
                    l_instDecidableEqString___boxed as *mut core::ffi::c_void,
                    2,
                    0,
                );
                v___x_1565_ =
                    l_Option_instDecidableEq___redArg(v___x_1564_, v_shell_1552_, v_shell_1557_);
                if v___x_1565_ == 0 {
                    crate::leanh::lean_dec(v_homeDir_1558_);
                    crate::leanh::lean_dec(v_homeDir_1553_);
                    return v___x_1565_;
                } else {
                    let mut v___x_1566_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                    let mut v___x_1567_: u8 = 0;
                    v___x_1566_ = crate::leanh::lean_alloc_closure(
                        l_System_instDecidableEqFilePath___boxed as *mut core::ffi::c_void,
                        2,
                        0,
                    );
                    v___x_1567_ = l_Option_instDecidableEq___redArg(
                        v___x_1566_,
                        v_homeDir_1553_,
                        v_homeDir_1558_,
                    );
                    return v___x_1567_;
                }
            }
        }
    }
}
pub unsafe fn l_Std_Async_System_instDecidableEqSystemUser_decEq___boxed(
    mut v_x_1568_: *mut crate::leanh::LeanObject,
    mut v_x_1569_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1570_: u8 = 0;
    let mut v_r_1571_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1570_ = l_Std_Async_System_instDecidableEqSystemUser_decEq(v_x_1568_, v_x_1569_);
    v_r_1571_ = crate::leanh::lean_box((v_res_1570_) as usize);
    return v_r_1571_;
}
pub unsafe fn l_Std_Async_System_instDecidableEqSystemUser(
    mut v_x_1572_: *mut crate::leanh::LeanObject,
    mut v_x_1573_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_1574_: u8 = 0;
    v___x_1574_ = l_Std_Async_System_instDecidableEqSystemUser_decEq(v_x_1572_, v_x_1573_);
    return v___x_1574_;
}
pub unsafe fn l_Std_Async_System_instDecidableEqSystemUser___boxed(
    mut v_x_1575_: *mut crate::leanh::LeanObject,
    mut v_x_1576_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1577_: u8 = 0;
    let mut v_r_1578_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1577_ = l_Std_Async_System_instDecidableEqSystemUser(v_x_1575_, v_x_1576_);
    v_r_1578_ = crate::leanh::lean_box((v_res_1577_) as usize);
    return v_r_1578_;
}
pub unsafe fn l_Option_repr___at___00Std_Async_System_instReprSystemUser_repr_spec__0(
    mut v_x_1585_: *mut crate::leanh::LeanObject,
    mut v_x_1586_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1587_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1588_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1590_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1591_: u8 = 0;
    let mut v___x_1592_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1593_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1594_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1595_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1597_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1598_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1599_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1600_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1601_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1602_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1603_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_1585_) == 0 {
                    v___x_1587_ = l_Option_repr___at___00Std_Async_System_instReprSystemUser_repr_spec__0___closed__1;
                    return v___x_1587_;
                } else {
                    v_val_1588_ = crate::leanh::lean_ctor_get(v_x_1585_, 0);
                    v_isSharedCheck_1603_ = (!crate::leanh::lean_is_exclusive(v_x_1585_)) as u8;
                    if v_isSharedCheck_1603_ == 0 {
                        v___x_1590_ = v_x_1585_;
                        v_isShared_1591_ = v_isSharedCheck_1603_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_val_1588_);
                        crate::leanh::lean_dec(v_x_1585_);
                        v___x_1590_ = crate::leanh::lean_box(0);
                        v_isShared_1591_ = v_isSharedCheck_1603_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_1592_ = l_Option_repr___at___00Std_Async_System_instReprSystemUser_repr_spec__0___closed__3;
                v___x_1593_ = crate::leanh::lean_unsigned_to_nat(1024);
                v___x_1594_ = l_Std_Async_System_instReprUserId___lam__0___closed__1;
                v___x_1595_ = l_Nat_reprFast(v_val_1588_);
                if v_isShared_1591_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_1590_, 3);
                    crate::leanh::lean_ctor_set(v___x_1590_, 0, v___x_1595_);
                    v___x_1597_ = v___x_1590_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1602_ = crate::leanh::lean_alloc_ctor(3, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1602_, 0, v___x_1595_);
                    v___x_1597_ = v_reuseFailAlloc_1602_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_1598_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1598_, 0, v___x_1594_);
                crate::leanh::lean_ctor_set(v___x_1598_, 1, v___x_1597_);
                v___x_1599_ = l_Repr_addAppParen(v___x_1598_, v___x_1593_);
                v___x_1600_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1600_, 0, v___x_1592_);
                crate::leanh::lean_ctor_set(v___x_1600_, 1, v___x_1599_);
                v___x_1601_ = l_Repr_addAppParen(v___x_1600_, v_x_1586_);
                return v___x_1601_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Option_repr___at___00Std_Async_System_instReprSystemUser_repr_spec__0___boxed(
    mut v_x_1604_: *mut crate::leanh::LeanObject,
    mut v_x_1605_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1606_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1606_ = l_Option_repr___at___00Std_Async_System_instReprSystemUser_repr_spec__0(
        v_x_1604_, v_x_1605_,
    );
    crate::leanh::lean_dec(v_x_1605_);
    return v_res_1606_;
}
pub unsafe fn l_Option_repr___at___00Std_Async_System_instReprSystemUser_repr_spec__1(
    mut v_x_1607_: *mut crate::leanh::LeanObject,
    mut v_x_1608_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1609_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1610_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1612_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1613_: u8 = 0;
    let mut v___x_1614_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1615_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1616_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1617_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1619_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1620_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1621_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1622_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1623_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1624_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1625_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_1607_) == 0 {
                    v___x_1609_ = l_Option_repr___at___00Std_Async_System_instReprSystemUser_repr_spec__0___closed__1;
                    return v___x_1609_;
                } else {
                    v_val_1610_ = crate::leanh::lean_ctor_get(v_x_1607_, 0);
                    v_isSharedCheck_1625_ = (!crate::leanh::lean_is_exclusive(v_x_1607_)) as u8;
                    if v_isSharedCheck_1625_ == 0 {
                        v___x_1612_ = v_x_1607_;
                        v_isShared_1613_ = v_isSharedCheck_1625_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_val_1610_);
                        crate::leanh::lean_dec(v_x_1607_);
                        v___x_1612_ = crate::leanh::lean_box(0);
                        v_isShared_1613_ = v_isSharedCheck_1625_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_1614_ = l_Option_repr___at___00Std_Async_System_instReprSystemUser_repr_spec__0___closed__3;
                v___x_1615_ = crate::leanh::lean_unsigned_to_nat(1024);
                v___x_1616_ = l_Std_Async_System_instReprGroupId___lam__0___closed__1;
                v___x_1617_ = l_Nat_reprFast(v_val_1610_);
                if v_isShared_1613_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_1612_, 3);
                    crate::leanh::lean_ctor_set(v___x_1612_, 0, v___x_1617_);
                    v___x_1619_ = v___x_1612_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1624_ = crate::leanh::lean_alloc_ctor(3, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1624_, 0, v___x_1617_);
                    v___x_1619_ = v_reuseFailAlloc_1624_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_1620_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1620_, 0, v___x_1616_);
                crate::leanh::lean_ctor_set(v___x_1620_, 1, v___x_1619_);
                v___x_1621_ = l_Repr_addAppParen(v___x_1620_, v___x_1615_);
                v___x_1622_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1622_, 0, v___x_1614_);
                crate::leanh::lean_ctor_set(v___x_1622_, 1, v___x_1621_);
                v___x_1623_ = l_Repr_addAppParen(v___x_1622_, v_x_1608_);
                return v___x_1623_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Option_repr___at___00Std_Async_System_instReprSystemUser_repr_spec__1___boxed(
    mut v_x_1626_: *mut crate::leanh::LeanObject,
    mut v_x_1627_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1628_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1628_ = l_Option_repr___at___00Std_Async_System_instReprSystemUser_repr_spec__1(
        v_x_1626_, v_x_1627_,
    );
    crate::leanh::lean_dec(v_x_1627_);
    return v_res_1628_;
}
pub unsafe fn l_Option_repr___at___00Std_Async_System_instReprSystemUser_repr_spec__2(
    mut v_x_1629_: *mut crate::leanh::LeanObject,
    mut v_x_1630_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1631_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1632_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1634_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1635_: u8 = 0;
    let mut v___x_1636_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1637_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1639_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1640_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1641_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1642_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1643_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_1629_) == 0 {
                    v___x_1631_ = l_Option_repr___at___00Std_Async_System_instReprSystemUser_repr_spec__0___closed__1;
                    return v___x_1631_;
                } else {
                    v_val_1632_ = crate::leanh::lean_ctor_get(v_x_1629_, 0);
                    v_isSharedCheck_1643_ = (!crate::leanh::lean_is_exclusive(v_x_1629_)) as u8;
                    if v_isSharedCheck_1643_ == 0 {
                        v___x_1634_ = v_x_1629_;
                        v_isShared_1635_ = v_isSharedCheck_1643_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_val_1632_);
                        crate::leanh::lean_dec(v_x_1629_);
                        v___x_1634_ = crate::leanh::lean_box(0);
                        v_isShared_1635_ = v_isSharedCheck_1643_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_1636_ = l_Option_repr___at___00Std_Async_System_instReprSystemUser_repr_spec__0___closed__3;
                v___x_1637_ = l_String_quote(v_val_1632_);
                if v_isShared_1635_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_1634_, 3);
                    crate::leanh::lean_ctor_set(v___x_1634_, 0, v___x_1637_);
                    v___x_1639_ = v___x_1634_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1642_ = crate::leanh::lean_alloc_ctor(3, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1642_, 0, v___x_1637_);
                    v___x_1639_ = v_reuseFailAlloc_1642_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_1640_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1640_, 0, v___x_1636_);
                crate::leanh::lean_ctor_set(v___x_1640_, 1, v___x_1639_);
                v___x_1641_ = l_Repr_addAppParen(v___x_1640_, v_x_1630_);
                return v___x_1641_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Option_repr___at___00Std_Async_System_instReprSystemUser_repr_spec__2___boxed(
    mut v_x_1644_: *mut crate::leanh::LeanObject,
    mut v_x_1645_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1646_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1646_ = l_Option_repr___at___00Std_Async_System_instReprSystemUser_repr_spec__2(
        v_x_1644_, v_x_1645_,
    );
    crate::leanh::lean_dec(v_x_1645_);
    return v_res_1646_;
}
pub unsafe fn l_Option_repr___at___00Std_Async_System_instReprSystemUser_repr_spec__3(
    mut v_x_1650_: *mut crate::leanh::LeanObject,
    mut v_x_1651_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1652_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1653_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1655_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1656_: u8 = 0;
    let mut v___x_1657_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1658_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1659_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1660_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1662_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1663_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1664_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1665_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1666_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1667_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1668_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_1650_) == 0 {
                    v___x_1652_ = l_Option_repr___at___00Std_Async_System_instReprSystemUser_repr_spec__0___closed__1;
                    return v___x_1652_;
                } else {
                    v_val_1653_ = crate::leanh::lean_ctor_get(v_x_1650_, 0);
                    v_isSharedCheck_1668_ = (!crate::leanh::lean_is_exclusive(v_x_1650_)) as u8;
                    if v_isSharedCheck_1668_ == 0 {
                        v___x_1655_ = v_x_1650_;
                        v_isShared_1656_ = v_isSharedCheck_1668_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_val_1653_);
                        crate::leanh::lean_dec(v_x_1650_);
                        v___x_1655_ = crate::leanh::lean_box(0);
                        v_isShared_1656_ = v_isSharedCheck_1668_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_1657_ = l_Option_repr___at___00Std_Async_System_instReprSystemUser_repr_spec__0___closed__3;
                v___x_1658_ = crate::leanh::lean_unsigned_to_nat(1024);
                v___x_1659_ = l_Option_repr___at___00Std_Async_System_instReprSystemUser_repr_spec__3___closed__1;
                v___x_1660_ = l_String_quote(v_val_1653_);
                if v_isShared_1656_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_1655_, 3);
                    crate::leanh::lean_ctor_set(v___x_1655_, 0, v___x_1660_);
                    v___x_1662_ = v___x_1655_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1667_ = crate::leanh::lean_alloc_ctor(3, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1667_, 0, v___x_1660_);
                    v___x_1662_ = v_reuseFailAlloc_1667_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_1663_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1663_, 0, v___x_1659_);
                crate::leanh::lean_ctor_set(v___x_1663_, 1, v___x_1662_);
                v___x_1664_ = l_Repr_addAppParen(v___x_1663_, v___x_1658_);
                v___x_1665_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1665_, 0, v___x_1657_);
                crate::leanh::lean_ctor_set(v___x_1665_, 1, v___x_1664_);
                v___x_1666_ = l_Repr_addAppParen(v___x_1665_, v_x_1651_);
                return v___x_1666_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Option_repr___at___00Std_Async_System_instReprSystemUser_repr_spec__3___boxed(
    mut v_x_1669_: *mut crate::leanh::LeanObject,
    mut v_x_1670_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1671_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1671_ = l_Option_repr___at___00Std_Async_System_instReprSystemUser_repr_spec__3(
        v_x_1669_, v_x_1670_,
    );
    crate::leanh::lean_dec(v_x_1670_);
    return v_res_1671_;
}
pub unsafe fn l_Nat_cast___at___00Std_Async_System_instReprSystemUser_repr_spec__4(
    mut v_a_1672_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1673_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1673_ = lean_nat_to_int(v_a_1672_);
    return v___x_1673_;
}
pub unsafe fn _init_l_Std_Async_System_instReprSystemUser_repr___redArg___closed__7()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1687_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1688_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1687_ = crate::leanh::lean_unsigned_to_nat(12);
    v___x_1688_ = lean_nat_to_int(v___x_1687_);
    return v___x_1688_;
}
pub unsafe fn _init_l_Std_Async_System_instReprSystemUser_repr___redArg___closed__12()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1695_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1696_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1695_ = crate::leanh::lean_unsigned_to_nat(10);
    v___x_1696_ = lean_nat_to_int(v___x_1695_);
    return v___x_1696_;
}
pub unsafe fn _init_l_Std_Async_System_instReprSystemUser_repr___redArg___closed__15()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1700_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1701_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1700_ = crate::leanh::lean_unsigned_to_nat(11);
    v___x_1701_ = lean_nat_to_int(v___x_1700_);
    return v___x_1701_;
}
pub unsafe fn _init_l_Std_Async_System_instReprSystemUser_repr___redArg___closed__18()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1705_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1706_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1705_ = crate::leanh::lean_unsigned_to_nat(9);
    v___x_1706_ = lean_nat_to_int(v___x_1705_);
    return v___x_1706_;
}
pub unsafe fn _init_l_Std_Async_System_instReprSystemUser_repr___redArg___closed__22()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1711_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1712_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1711_ = l_Std_Async_System_instReprSystemUser_repr___redArg___closed__0;
    v___x_1712_ = lean_string_length(v___x_1711_);
    return v___x_1712_;
}
pub unsafe fn _init_l_Std_Async_System_instReprSystemUser_repr___redArg___closed__23()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1713_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1714_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1713_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Async_System_instReprSystemUser_repr___redArg___closed__22),
        core::ptr::addr_of_mut!(
            l_Std_Async_System_instReprSystemUser_repr___redArg___closed__22_once
        ),
        _init_l_Std_Async_System_instReprSystemUser_repr___redArg___closed__22,
    );
    v___x_1714_ = lean_nat_to_int(v___x_1713_);
    return v___x_1714_;
}
pub unsafe fn l_Std_Async_System_instReprSystemUser_repr___redArg(
    mut v_x_1719_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_username_1720_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_userId_1721_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_groupId_1722_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_shell_1723_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_homeDir_1724_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1725_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1726_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1727_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1728_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1729_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1730_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1731_: u8 = 0;
    let mut v___x_1732_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1733_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1734_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1735_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1736_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1737_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1738_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1739_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1740_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1741_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1742_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1743_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1744_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1745_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1746_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1747_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1748_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1749_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1750_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1751_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1752_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1753_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1754_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1755_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1756_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1757_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1758_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1759_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1760_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1761_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1762_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1763_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1764_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1765_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1766_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1767_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1768_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1769_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1770_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1771_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1772_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1773_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1774_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1775_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1776_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1777_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1778_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1779_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1780_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1781_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1782_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_username_1720_ = crate::leanh::lean_ctor_get(v_x_1719_, 0);
    crate::leanh::lean_inc_ref(v_username_1720_);
    v_userId_1721_ = crate::leanh::lean_ctor_get(v_x_1719_, 1);
    crate::leanh::lean_inc(v_userId_1721_);
    v_groupId_1722_ = crate::leanh::lean_ctor_get(v_x_1719_, 2);
    crate::leanh::lean_inc(v_groupId_1722_);
    v_shell_1723_ = crate::leanh::lean_ctor_get(v_x_1719_, 3);
    crate::leanh::lean_inc(v_shell_1723_);
    v_homeDir_1724_ = crate::leanh::lean_ctor_get(v_x_1719_, 4);
    crate::leanh::lean_inc(v_homeDir_1724_);
    crate::leanh::lean_dec_ref(v_x_1719_);
    v___x_1725_ = l_Std_Async_System_instReprSystemUser_repr___redArg___closed__5;
    v___x_1726_ = l_Std_Async_System_instReprSystemUser_repr___redArg___closed__6;
    v___x_1727_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Async_System_instReprSystemUser_repr___redArg___closed__7),
        core::ptr::addr_of_mut!(
            l_Std_Async_System_instReprSystemUser_repr___redArg___closed__7_once
        ),
        _init_l_Std_Async_System_instReprSystemUser_repr___redArg___closed__7,
    );
    v___x_1728_ = l_String_quote(v_username_1720_);
    v___x_1729_ = crate::leanh::lean_alloc_ctor(3, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1729_, 0, v___x_1728_);
    v___x_1730_ = crate::leanh::lean_alloc_ctor(4, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1730_, 0, v___x_1727_);
    crate::leanh::lean_ctor_set(v___x_1730_, 1, v___x_1729_);
    v___x_1731_ = 0;
    v___x_1732_ = crate::leanh::lean_alloc_ctor(6, 1, (1) as u32);
    crate::leanh::lean_ctor_set(v___x_1732_, 0, v___x_1730_);
    crate::leanh::lean_ctor_set_uint8(
        v___x_1732_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
        v___x_1731_,
    );
    v___x_1733_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1733_, 0, v___x_1726_);
    crate::leanh::lean_ctor_set(v___x_1733_, 1, v___x_1732_);
    v___x_1734_ = l_Std_Async_System_instReprSystemUser_repr___redArg___closed__9;
    v___x_1735_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1735_, 0, v___x_1733_);
    crate::leanh::lean_ctor_set(v___x_1735_, 1, v___x_1734_);
    v___x_1736_ = crate::leanh::lean_box(1);
    v___x_1737_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1737_, 0, v___x_1735_);
    crate::leanh::lean_ctor_set(v___x_1737_, 1, v___x_1736_);
    v___x_1738_ = l_Std_Async_System_instReprSystemUser_repr___redArg___closed__11;
    v___x_1739_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1739_, 0, v___x_1737_);
    crate::leanh::lean_ctor_set(v___x_1739_, 1, v___x_1738_);
    v___x_1740_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1740_, 0, v___x_1739_);
    crate::leanh::lean_ctor_set(v___x_1740_, 1, v___x_1725_);
    v___x_1741_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Async_System_instReprSystemUser_repr___redArg___closed__12),
        core::ptr::addr_of_mut!(
            l_Std_Async_System_instReprSystemUser_repr___redArg___closed__12_once
        ),
        _init_l_Std_Async_System_instReprSystemUser_repr___redArg___closed__12,
    );
    v___x_1742_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_1743_ = l_Option_repr___at___00Std_Async_System_instReprSystemUser_repr_spec__0(
        v_userId_1721_,
        v___x_1742_,
    );
    v___x_1744_ = crate::leanh::lean_alloc_ctor(4, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1744_, 0, v___x_1741_);
    crate::leanh::lean_ctor_set(v___x_1744_, 1, v___x_1743_);
    v___x_1745_ = crate::leanh::lean_alloc_ctor(6, 1, (1) as u32);
    crate::leanh::lean_ctor_set(v___x_1745_, 0, v___x_1744_);
    crate::leanh::lean_ctor_set_uint8(
        v___x_1745_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
        v___x_1731_,
    );
    v___x_1746_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1746_, 0, v___x_1740_);
    crate::leanh::lean_ctor_set(v___x_1746_, 1, v___x_1745_);
    v___x_1747_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1747_, 0, v___x_1746_);
    crate::leanh::lean_ctor_set(v___x_1747_, 1, v___x_1734_);
    v___x_1748_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1748_, 0, v___x_1747_);
    crate::leanh::lean_ctor_set(v___x_1748_, 1, v___x_1736_);
    v___x_1749_ = l_Std_Async_System_instReprSystemUser_repr___redArg___closed__14;
    v___x_1750_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1750_, 0, v___x_1748_);
    crate::leanh::lean_ctor_set(v___x_1750_, 1, v___x_1749_);
    v___x_1751_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1751_, 0, v___x_1750_);
    crate::leanh::lean_ctor_set(v___x_1751_, 1, v___x_1725_);
    v___x_1752_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Async_System_instReprSystemUser_repr___redArg___closed__15),
        core::ptr::addr_of_mut!(
            l_Std_Async_System_instReprSystemUser_repr___redArg___closed__15_once
        ),
        _init_l_Std_Async_System_instReprSystemUser_repr___redArg___closed__15,
    );
    v___x_1753_ = l_Option_repr___at___00Std_Async_System_instReprSystemUser_repr_spec__1(
        v_groupId_1722_,
        v___x_1742_,
    );
    v___x_1754_ = crate::leanh::lean_alloc_ctor(4, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1754_, 0, v___x_1752_);
    crate::leanh::lean_ctor_set(v___x_1754_, 1, v___x_1753_);
    v___x_1755_ = crate::leanh::lean_alloc_ctor(6, 1, (1) as u32);
    crate::leanh::lean_ctor_set(v___x_1755_, 0, v___x_1754_);
    crate::leanh::lean_ctor_set_uint8(
        v___x_1755_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
        v___x_1731_,
    );
    v___x_1756_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1756_, 0, v___x_1751_);
    crate::leanh::lean_ctor_set(v___x_1756_, 1, v___x_1755_);
    v___x_1757_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1757_, 0, v___x_1756_);
    crate::leanh::lean_ctor_set(v___x_1757_, 1, v___x_1734_);
    v___x_1758_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1758_, 0, v___x_1757_);
    crate::leanh::lean_ctor_set(v___x_1758_, 1, v___x_1736_);
    v___x_1759_ = l_Std_Async_System_instReprSystemUser_repr___redArg___closed__17;
    v___x_1760_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1760_, 0, v___x_1758_);
    crate::leanh::lean_ctor_set(v___x_1760_, 1, v___x_1759_);
    v___x_1761_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1761_, 0, v___x_1760_);
    crate::leanh::lean_ctor_set(v___x_1761_, 1, v___x_1725_);
    v___x_1762_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Async_System_instReprSystemUser_repr___redArg___closed__18),
        core::ptr::addr_of_mut!(
            l_Std_Async_System_instReprSystemUser_repr___redArg___closed__18_once
        ),
        _init_l_Std_Async_System_instReprSystemUser_repr___redArg___closed__18,
    );
    v___x_1763_ = l_Option_repr___at___00Std_Async_System_instReprSystemUser_repr_spec__2(
        v_shell_1723_,
        v___x_1742_,
    );
    v___x_1764_ = crate::leanh::lean_alloc_ctor(4, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1764_, 0, v___x_1762_);
    crate::leanh::lean_ctor_set(v___x_1764_, 1, v___x_1763_);
    v___x_1765_ = crate::leanh::lean_alloc_ctor(6, 1, (1) as u32);
    crate::leanh::lean_ctor_set(v___x_1765_, 0, v___x_1764_);
    crate::leanh::lean_ctor_set_uint8(
        v___x_1765_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
        v___x_1731_,
    );
    v___x_1766_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1766_, 0, v___x_1761_);
    crate::leanh::lean_ctor_set(v___x_1766_, 1, v___x_1765_);
    v___x_1767_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1767_, 0, v___x_1766_);
    crate::leanh::lean_ctor_set(v___x_1767_, 1, v___x_1734_);
    v___x_1768_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1768_, 0, v___x_1767_);
    crate::leanh::lean_ctor_set(v___x_1768_, 1, v___x_1736_);
    v___x_1769_ = l_Std_Async_System_instReprSystemUser_repr___redArg___closed__20;
    v___x_1770_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1770_, 0, v___x_1768_);
    crate::leanh::lean_ctor_set(v___x_1770_, 1, v___x_1769_);
    v___x_1771_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1771_, 0, v___x_1770_);
    crate::leanh::lean_ctor_set(v___x_1771_, 1, v___x_1725_);
    v___x_1772_ = l_Option_repr___at___00Std_Async_System_instReprSystemUser_repr_spec__3(
        v_homeDir_1724_,
        v___x_1742_,
    );
    v___x_1773_ = crate::leanh::lean_alloc_ctor(4, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1773_, 0, v___x_1752_);
    crate::leanh::lean_ctor_set(v___x_1773_, 1, v___x_1772_);
    v___x_1774_ = crate::leanh::lean_alloc_ctor(6, 1, (1) as u32);
    crate::leanh::lean_ctor_set(v___x_1774_, 0, v___x_1773_);
    crate::leanh::lean_ctor_set_uint8(
        v___x_1774_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
        v___x_1731_,
    );
    v___x_1775_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1775_, 0, v___x_1771_);
    crate::leanh::lean_ctor_set(v___x_1775_, 1, v___x_1774_);
    v___x_1776_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Async_System_instReprSystemUser_repr___redArg___closed__23),
        core::ptr::addr_of_mut!(
            l_Std_Async_System_instReprSystemUser_repr___redArg___closed__23_once
        ),
        _init_l_Std_Async_System_instReprSystemUser_repr___redArg___closed__23,
    );
    v___x_1777_ = l_Std_Async_System_instReprSystemUser_repr___redArg___closed__24;
    v___x_1778_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1778_, 0, v___x_1777_);
    crate::leanh::lean_ctor_set(v___x_1778_, 1, v___x_1775_);
    v___x_1779_ = l_Std_Async_System_instReprSystemUser_repr___redArg___closed__25;
    v___x_1780_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1780_, 0, v___x_1778_);
    crate::leanh::lean_ctor_set(v___x_1780_, 1, v___x_1779_);
    v___x_1781_ = crate::leanh::lean_alloc_ctor(4, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1781_, 0, v___x_1776_);
    crate::leanh::lean_ctor_set(v___x_1781_, 1, v___x_1780_);
    v___x_1782_ = crate::leanh::lean_alloc_ctor(6, 1, (1) as u32);
    crate::leanh::lean_ctor_set(v___x_1782_, 0, v___x_1781_);
    crate::leanh::lean_ctor_set_uint8(
        v___x_1782_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
        v___x_1731_,
    );
    return v___x_1782_;
}
pub unsafe fn l_Std_Async_System_instReprSystemUser_repr(
    mut v_x_1783_: *mut crate::leanh::LeanObject,
    mut v_prec_1784_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1785_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1785_ = l_Std_Async_System_instReprSystemUser_repr___redArg(v_x_1783_);
    return v___x_1785_;
}
pub unsafe fn l_Std_Async_System_instReprSystemUser_repr___boxed(
    mut v_x_1786_: *mut crate::leanh::LeanObject,
    mut v_prec_1787_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1788_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1788_ = l_Std_Async_System_instReprSystemUser_repr(v_x_1786_, v_prec_1787_);
    crate::leanh::lean_dec(v_prec_1787_);
    return v_res_1788_;
}
pub unsafe fn l_Std_Format_joinSep___at___00Array_repr___at___00Std_Async_System_instReprGroupInfo_repr_spec__0_spec__0___lam__0(
    mut v___y_1791_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1792_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1793_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1792_ = l_String_quote(v___y_1791_);
    v___x_1793_ = crate::leanh::lean_alloc_ctor(3, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1793_, 0, v___x_1792_);
    return v___x_1793_;
}
pub unsafe fn l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Std_Async_System_instReprGroupInfo_repr_spec__0_spec__0_spec__1_spec__2(
    mut v_x_1794_: *mut crate::leanh::LeanObject,
    mut v_x_1795_: *mut crate::leanh::LeanObject,
    mut v_x_1796_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_head_1797_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_1798_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1800_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1801_: u8 = 0;
    let mut v___x_1803_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1804_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1805_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1806_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1808_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1809_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_1796_) == 0 {
                    crate::leanh::lean_dec(v_x_1794_);
                    return v_x_1795_;
                } else {
                    v_head_1797_ = crate::leanh::lean_ctor_get(v_x_1796_, 0);
                    v_tail_1798_ = crate::leanh::lean_ctor_get(v_x_1796_, 1);
                    v_isSharedCheck_1809_ = (!crate::leanh::lean_is_exclusive(v_x_1796_)) as u8;
                    if v_isSharedCheck_1809_ == 0 {
                        v___x_1800_ = v_x_1796_;
                        v_isShared_1801_ = v_isSharedCheck_1809_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_tail_1798_);
                        crate::leanh::lean_inc(v_head_1797_);
                        crate::leanh::lean_dec(v_x_1796_);
                        v___x_1800_ = crate::leanh::lean_box(0);
                        v_isShared_1801_ = v_isSharedCheck_1809_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                crate::leanh::lean_inc(v_x_1794_);
                if v_isShared_1801_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_1800_, 5);
                    crate::leanh::lean_ctor_set(v___x_1800_, 1, v_x_1794_);
                    crate::leanh::lean_ctor_set(v___x_1800_, 0, v_x_1795_);
                    v___x_1803_ = v___x_1800_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1808_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1808_, 0, v_x_1795_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1808_, 1, v_x_1794_);
                    v___x_1803_ = v_reuseFailAlloc_1808_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_1804_ = l_String_quote(v_head_1797_);
                v___x_1805_ = crate::leanh::lean_alloc_ctor(3, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1805_, 0, v___x_1804_);
                v___x_1806_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1806_, 0, v___x_1803_);
                crate::leanh::lean_ctor_set(v___x_1806_, 1, v___x_1805_);
                v_x_1795_ = v___x_1806_;
                v_x_1796_ = v_tail_1798_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Std_Async_System_instReprGroupInfo_repr_spec__0_spec__0_spec__1(
    mut v_x_1810_: *mut crate::leanh::LeanObject,
    mut v_x_1811_: *mut crate::leanh::LeanObject,
    mut v_x_1812_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_head_1813_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_1814_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1816_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1817_: u8 = 0;
    let mut v___x_1819_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1820_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1821_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1822_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1823_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1824_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1825_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_1812_) == 0 {
                    crate::leanh::lean_dec(v_x_1810_);
                    return v_x_1811_;
                } else {
                    v_head_1813_ = crate::leanh::lean_ctor_get(v_x_1812_, 0);
                    v_tail_1814_ = crate::leanh::lean_ctor_get(v_x_1812_, 1);
                    v_isSharedCheck_1825_ = (!crate::leanh::lean_is_exclusive(v_x_1812_)) as u8;
                    if v_isSharedCheck_1825_ == 0 {
                        v___x_1816_ = v_x_1812_;
                        v_isShared_1817_ = v_isSharedCheck_1825_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_tail_1814_);
                        crate::leanh::lean_inc(v_head_1813_);
                        crate::leanh::lean_dec(v_x_1812_);
                        v___x_1816_ = crate::leanh::lean_box(0);
                        v_isShared_1817_ = v_isSharedCheck_1825_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                crate::leanh::lean_inc(v_x_1810_);
                if v_isShared_1817_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_1816_, 5);
                    crate::leanh::lean_ctor_set(v___x_1816_, 1, v_x_1810_);
                    crate::leanh::lean_ctor_set(v___x_1816_, 0, v_x_1811_);
                    v___x_1819_ = v___x_1816_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1824_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1824_, 0, v_x_1811_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1824_, 1, v_x_1810_);
                    v___x_1819_ = v_reuseFailAlloc_1824_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_1820_ = l_String_quote(v_head_1813_);
                v___x_1821_ = crate::leanh::lean_alloc_ctor(3, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1821_, 0, v___x_1820_);
                v___x_1822_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1822_, 0, v___x_1819_);
                crate::leanh::lean_ctor_set(v___x_1822_, 1, v___x_1821_);
                v___x_1823_ = l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Std_Async_System_instReprGroupInfo_repr_spec__0_spec__0_spec__1_spec__2(v_x_1810_, v___x_1822_, v_tail_1814_);
                return v___x_1823_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Format_joinSep___at___00Array_repr___at___00Std_Async_System_instReprGroupInfo_repr_spec__0_spec__0(
    mut v_x_1826_: *mut crate::leanh::LeanObject,
    mut v_x_1827_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_1826_) == 0 {
        let mut v___x_1828_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_x_1827_);
        v___x_1828_ = crate::leanh::lean_box(0);
        return v___x_1828_;
    } else {
        let mut v_tail_1829_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_tail_1829_ = crate::leanh::lean_ctor_get(v_x_1826_, 1);
        if crate::leanh::lean_obj_tag(v_tail_1829_) == 0 {
            let mut v_head_1830_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1831_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_x_1827_);
            v_head_1830_ = crate::leanh::lean_ctor_get(v_x_1826_, 0);
            crate::leanh::lean_inc(v_head_1830_);
            crate::leanh::lean_dec_ref_known(v_x_1826_, 2);
            v___x_1831_ = l_Std_Format_joinSep___at___00Array_repr___at___00Std_Async_System_instReprGroupInfo_repr_spec__0_spec__0___lam__0(v_head_1830_);
            return v___x_1831_;
        } else {
            let mut v_head_1832_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1833_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1834_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_inc(v_tail_1829_);
            v_head_1832_ = crate::leanh::lean_ctor_get(v_x_1826_, 0);
            crate::leanh::lean_inc(v_head_1832_);
            crate::leanh::lean_dec_ref_known(v_x_1826_, 2);
            v___x_1833_ = l_Std_Format_joinSep___at___00Array_repr___at___00Std_Async_System_instReprGroupInfo_repr_spec__0_spec__0___lam__0(v_head_1832_);
            v___x_1834_ = l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Std_Async_System_instReprGroupInfo_repr_spec__0_spec__0_spec__1(v_x_1827_, v___x_1833_, v_tail_1829_);
            return v___x_1834_;
        }
    }
}
pub unsafe fn _init_l_Array_repr___at___00Std_Async_System_instReprGroupInfo_repr_spec__0___closed__3()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1840_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1841_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1840_ = l_Array_repr___at___00Std_Async_System_instReprGroupInfo_repr_spec__0___closed__0;
    v___x_1841_ = lean_string_length(v___x_1840_);
    return v___x_1841_;
}
pub unsafe fn _init_l_Array_repr___at___00Std_Async_System_instReprGroupInfo_repr_spec__0___closed__4()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1842_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1843_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1842_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Array_repr___at___00Std_Async_System_instReprGroupInfo_repr_spec__0___closed__3
        ),
        core::ptr::addr_of_mut!(
            l_Array_repr___at___00Std_Async_System_instReprGroupInfo_repr_spec__0___closed__3_once
        ),
        _init_l_Array_repr___at___00Std_Async_System_instReprGroupInfo_repr_spec__0___closed__3,
    );
    v___x_1843_ = lean_nat_to_int(v___x_1842_);
    return v___x_1843_;
}
pub unsafe fn l_Array_repr___at___00Std_Async_System_instReprGroupInfo_repr_spec__0(
    mut v_xs_1851_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1852_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1853_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1854_: u8 = 0;
    v___x_1852_ = lean_array_get_size(v_xs_1851_);
    v___x_1853_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_1854_ = lean_nat_dec_eq(v___x_1852_, v___x_1853_);
    if v___x_1854_ == 0 {
        let mut v___x_1855_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1856_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1857_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1858_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1859_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1860_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1861_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1862_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1863_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1864_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_1855_ = lean_array_to_list(v_xs_1851_);
        v___x_1856_ =
            l_Array_repr___at___00Std_Async_System_instReprGroupInfo_repr_spec__0___closed__1;
        v___x_1857_ = l_Std_Format_joinSep___at___00Array_repr___at___00Std_Async_System_instReprGroupInfo_repr_spec__0_spec__0(v___x_1855_, v___x_1856_);
        v___x_1858_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Array_repr___at___00Std_Async_System_instReprGroupInfo_repr_spec__0___closed__4), core::ptr::addr_of_mut!(l_Array_repr___at___00Std_Async_System_instReprGroupInfo_repr_spec__0___closed__4_once), _init_l_Array_repr___at___00Std_Async_System_instReprGroupInfo_repr_spec__0___closed__4);
        v___x_1859_ =
            l_Array_repr___at___00Std_Async_System_instReprGroupInfo_repr_spec__0___closed__5;
        v___x_1860_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_1860_, 0, v___x_1859_);
        crate::leanh::lean_ctor_set(v___x_1860_, 1, v___x_1857_);
        v___x_1861_ =
            l_Array_repr___at___00Std_Async_System_instReprGroupInfo_repr_spec__0___closed__6;
        v___x_1862_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_1862_, 0, v___x_1860_);
        crate::leanh::lean_ctor_set(v___x_1862_, 1, v___x_1861_);
        v___x_1863_ = crate::leanh::lean_alloc_ctor(4, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_1863_, 0, v___x_1858_);
        crate::leanh::lean_ctor_set(v___x_1863_, 1, v___x_1862_);
        v___x_1864_ = l_Std_Format_fill(v___x_1863_);
        return v___x_1864_;
    } else {
        let mut v___x_1865_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec_ref(v_xs_1851_);
        v___x_1865_ =
            l_Array_repr___at___00Std_Async_System_instReprGroupInfo_repr_spec__0___closed__8;
        return v___x_1865_;
    }
}
pub unsafe fn _init_l_Std_Async_System_instReprGroupInfo_repr___redArg___closed__4()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1875_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1876_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1875_ = crate::leanh::lean_unsigned_to_nat(13);
    v___x_1876_ = lean_nat_to_int(v___x_1875_);
    return v___x_1876_;
}
pub unsafe fn l_Std_Async_System_instReprGroupInfo_repr___redArg(
    mut v_x_1880_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_groupName_1881_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_groupId_1882_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_members_1883_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1884_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1885_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1886_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1887_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1888_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1889_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1890_: u8 = 0;
    let mut v___x_1891_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1892_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1893_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1894_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1895_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1896_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1897_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1898_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1899_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1900_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1901_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1902_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1903_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1904_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1905_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1906_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1907_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1908_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1909_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1910_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1911_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1912_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1913_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1914_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1915_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1916_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1917_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1918_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1919_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1920_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1921_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1922_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1923_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1924_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1925_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_groupName_1881_ = crate::leanh::lean_ctor_get(v_x_1880_, 0);
    crate::leanh::lean_inc_ref(v_groupName_1881_);
    v_groupId_1882_ = crate::leanh::lean_ctor_get(v_x_1880_, 1);
    crate::leanh::lean_inc(v_groupId_1882_);
    v_members_1883_ = crate::leanh::lean_ctor_get(v_x_1880_, 2);
    crate::leanh::lean_inc_ref(v_members_1883_);
    crate::leanh::lean_dec_ref(v_x_1880_);
    v___x_1884_ = l_Std_Async_System_instReprSystemUser_repr___redArg___closed__5;
    v___x_1885_ = l_Std_Async_System_instReprGroupInfo_repr___redArg___closed__3;
    v___x_1886_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Async_System_instReprGroupInfo_repr___redArg___closed__4),
        core::ptr::addr_of_mut!(
            l_Std_Async_System_instReprGroupInfo_repr___redArg___closed__4_once
        ),
        _init_l_Std_Async_System_instReprGroupInfo_repr___redArg___closed__4,
    );
    v___x_1887_ = l_String_quote(v_groupName_1881_);
    v___x_1888_ = crate::leanh::lean_alloc_ctor(3, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1888_, 0, v___x_1887_);
    v___x_1889_ = crate::leanh::lean_alloc_ctor(4, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1889_, 0, v___x_1886_);
    crate::leanh::lean_ctor_set(v___x_1889_, 1, v___x_1888_);
    v___x_1890_ = 0;
    v___x_1891_ = crate::leanh::lean_alloc_ctor(6, 1, (1) as u32);
    crate::leanh::lean_ctor_set(v___x_1891_, 0, v___x_1889_);
    crate::leanh::lean_ctor_set_uint8(
        v___x_1891_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
        v___x_1890_,
    );
    v___x_1892_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1892_, 0, v___x_1885_);
    crate::leanh::lean_ctor_set(v___x_1892_, 1, v___x_1891_);
    v___x_1893_ = l_Std_Async_System_instReprSystemUser_repr___redArg___closed__9;
    v___x_1894_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1894_, 0, v___x_1892_);
    crate::leanh::lean_ctor_set(v___x_1894_, 1, v___x_1893_);
    v___x_1895_ = crate::leanh::lean_box(1);
    v___x_1896_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1896_, 0, v___x_1894_);
    crate::leanh::lean_ctor_set(v___x_1896_, 1, v___x_1895_);
    v___x_1897_ = l_Std_Async_System_instReprSystemUser_repr___redArg___closed__14;
    v___x_1898_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1898_, 0, v___x_1896_);
    crate::leanh::lean_ctor_set(v___x_1898_, 1, v___x_1897_);
    v___x_1899_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1899_, 0, v___x_1898_);
    crate::leanh::lean_ctor_set(v___x_1899_, 1, v___x_1884_);
    v___x_1900_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Async_System_instReprSystemUser_repr___redArg___closed__15),
        core::ptr::addr_of_mut!(
            l_Std_Async_System_instReprSystemUser_repr___redArg___closed__15_once
        ),
        _init_l_Std_Async_System_instReprSystemUser_repr___redArg___closed__15,
    );
    v___x_1901_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_1902_ = l_Std_Async_System_instReprGroupId___lam__0___closed__1;
    v___x_1903_ = l_Nat_reprFast(v_groupId_1882_);
    v___x_1904_ = crate::leanh::lean_alloc_ctor(3, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1904_, 0, v___x_1903_);
    v___x_1905_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1905_, 0, v___x_1902_);
    crate::leanh::lean_ctor_set(v___x_1905_, 1, v___x_1904_);
    v___x_1906_ = l_Repr_addAppParen(v___x_1905_, v___x_1901_);
    v___x_1907_ = crate::leanh::lean_alloc_ctor(4, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1907_, 0, v___x_1900_);
    crate::leanh::lean_ctor_set(v___x_1907_, 1, v___x_1906_);
    v___x_1908_ = crate::leanh::lean_alloc_ctor(6, 1, (1) as u32);
    crate::leanh::lean_ctor_set(v___x_1908_, 0, v___x_1907_);
    crate::leanh::lean_ctor_set_uint8(
        v___x_1908_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
        v___x_1890_,
    );
    v___x_1909_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1909_, 0, v___x_1899_);
    crate::leanh::lean_ctor_set(v___x_1909_, 1, v___x_1908_);
    v___x_1910_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1910_, 0, v___x_1909_);
    crate::leanh::lean_ctor_set(v___x_1910_, 1, v___x_1893_);
    v___x_1911_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1911_, 0, v___x_1910_);
    crate::leanh::lean_ctor_set(v___x_1911_, 1, v___x_1895_);
    v___x_1912_ = l_Std_Async_System_instReprGroupInfo_repr___redArg___closed__6;
    v___x_1913_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1913_, 0, v___x_1911_);
    crate::leanh::lean_ctor_set(v___x_1913_, 1, v___x_1912_);
    v___x_1914_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1914_, 0, v___x_1913_);
    crate::leanh::lean_ctor_set(v___x_1914_, 1, v___x_1884_);
    v___x_1915_ =
        l_Array_repr___at___00Std_Async_System_instReprGroupInfo_repr_spec__0(v_members_1883_);
    v___x_1916_ = crate::leanh::lean_alloc_ctor(4, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1916_, 0, v___x_1900_);
    crate::leanh::lean_ctor_set(v___x_1916_, 1, v___x_1915_);
    v___x_1917_ = crate::leanh::lean_alloc_ctor(6, 1, (1) as u32);
    crate::leanh::lean_ctor_set(v___x_1917_, 0, v___x_1916_);
    crate::leanh::lean_ctor_set_uint8(
        v___x_1917_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
        v___x_1890_,
    );
    v___x_1918_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1918_, 0, v___x_1914_);
    crate::leanh::lean_ctor_set(v___x_1918_, 1, v___x_1917_);
    v___x_1919_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Async_System_instReprSystemUser_repr___redArg___closed__23),
        core::ptr::addr_of_mut!(
            l_Std_Async_System_instReprSystemUser_repr___redArg___closed__23_once
        ),
        _init_l_Std_Async_System_instReprSystemUser_repr___redArg___closed__23,
    );
    v___x_1920_ = l_Std_Async_System_instReprSystemUser_repr___redArg___closed__24;
    v___x_1921_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1921_, 0, v___x_1920_);
    crate::leanh::lean_ctor_set(v___x_1921_, 1, v___x_1918_);
    v___x_1922_ = l_Std_Async_System_instReprSystemUser_repr___redArg___closed__25;
    v___x_1923_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1923_, 0, v___x_1921_);
    crate::leanh::lean_ctor_set(v___x_1923_, 1, v___x_1922_);
    v___x_1924_ = crate::leanh::lean_alloc_ctor(4, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1924_, 0, v___x_1919_);
    crate::leanh::lean_ctor_set(v___x_1924_, 1, v___x_1923_);
    v___x_1925_ = crate::leanh::lean_alloc_ctor(6, 1, (1) as u32);
    crate::leanh::lean_ctor_set(v___x_1925_, 0, v___x_1924_);
    crate::leanh::lean_ctor_set_uint8(
        v___x_1925_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
        v___x_1890_,
    );
    return v___x_1925_;
}
pub unsafe fn l_Std_Async_System_instReprGroupInfo_repr(
    mut v_x_1926_: *mut crate::leanh::LeanObject,
    mut v_prec_1927_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1928_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1928_ = l_Std_Async_System_instReprGroupInfo_repr___redArg(v_x_1926_);
    return v___x_1928_;
}
pub unsafe fn l_Std_Async_System_instReprGroupInfo_repr___boxed(
    mut v_x_1929_: *mut crate::leanh::LeanObject,
    mut v_prec_1930_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1931_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1931_ = l_Std_Async_System_instReprGroupInfo_repr(v_x_1929_, v_prec_1930_);
    crate::leanh::lean_dec(v_prec_1930_);
    return v_res_1931_;
}
pub unsafe fn _init_l_Std_Async_System_instInhabitedCPUTimes_default___closed__0()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1942_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1943_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1942_ = l_Std_Time_Millisecond_instInhabitedOffset;
    v___x_1943_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1943_, 0, v___x_1942_);
    crate::leanh::lean_ctor_set(v___x_1943_, 1, v___x_1942_);
    crate::leanh::lean_ctor_set(v___x_1943_, 2, v___x_1942_);
    crate::leanh::lean_ctor_set(v___x_1943_, 3, v___x_1942_);
    crate::leanh::lean_ctor_set(v___x_1943_, 4, v___x_1942_);
    return v___x_1943_;
}
pub unsafe fn _init_l_Std_Async_System_instInhabitedCPUTimes_default()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1944_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1944_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Async_System_instInhabitedCPUTimes_default___closed__0),
        core::ptr::addr_of_mut!(l_Std_Async_System_instInhabitedCPUTimes_default___closed__0_once),
        _init_l_Std_Async_System_instInhabitedCPUTimes_default___closed__0,
    );
    return v___x_1944_;
}
pub unsafe fn _init_l_Std_Async_System_instInhabitedCPUTimes() -> *mut crate::leanh::LeanObject {
    let mut v___x_1945_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1945_ = l_Std_Async_System_instInhabitedCPUTimes_default;
    return v___x_1945_;
}
pub unsafe fn l_Std_Async_System_instDecidableEqCPUTimes_decEq(
    mut v_x_1946_: *mut crate::leanh::LeanObject,
    mut v_x_1947_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v_userTime_1948_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_niceTime_1949_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_systemTime_1950_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_idleTime_1951_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_interruptTime_1952_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_userTime_1953_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_niceTime_1954_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_systemTime_1955_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_idleTime_1956_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_interruptTime_1957_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1958_: u8 = 0;
    v_userTime_1948_ = crate::leanh::lean_ctor_get(v_x_1946_, 0);
    v_niceTime_1949_ = crate::leanh::lean_ctor_get(v_x_1946_, 1);
    v_systemTime_1950_ = crate::leanh::lean_ctor_get(v_x_1946_, 2);
    v_idleTime_1951_ = crate::leanh::lean_ctor_get(v_x_1946_, 3);
    v_interruptTime_1952_ = crate::leanh::lean_ctor_get(v_x_1946_, 4);
    v_userTime_1953_ = crate::leanh::lean_ctor_get(v_x_1947_, 0);
    v_niceTime_1954_ = crate::leanh::lean_ctor_get(v_x_1947_, 1);
    v_systemTime_1955_ = crate::leanh::lean_ctor_get(v_x_1947_, 2);
    v_idleTime_1956_ = crate::leanh::lean_ctor_get(v_x_1947_, 3);
    v_interruptTime_1957_ = crate::leanh::lean_ctor_get(v_x_1947_, 4);
    v___x_1958_ = lean_int_dec_eq(v_userTime_1948_, v_userTime_1953_);
    if v___x_1958_ == 0 {
        return v___x_1958_;
    } else {
        let mut v___x_1959_: u8 = 0;
        v___x_1959_ = lean_int_dec_eq(v_niceTime_1949_, v_niceTime_1954_);
        if v___x_1959_ == 0 {
            return v___x_1959_;
        } else {
            let mut v___x_1960_: u8 = 0;
            v___x_1960_ = lean_int_dec_eq(v_systemTime_1950_, v_systemTime_1955_);
            if v___x_1960_ == 0 {
                return v___x_1960_;
            } else {
                let mut v___x_1961_: u8 = 0;
                v___x_1961_ = lean_int_dec_eq(v_idleTime_1951_, v_idleTime_1956_);
                if v___x_1961_ == 0 {
                    return v___x_1961_;
                } else {
                    let mut v___x_1962_: u8 = 0;
                    v___x_1962_ = lean_int_dec_eq(v_interruptTime_1952_, v_interruptTime_1957_);
                    return v___x_1962_;
                }
            }
        }
    }
}
pub unsafe fn l_Std_Async_System_instDecidableEqCPUTimes_decEq___boxed(
    mut v_x_1963_: *mut crate::leanh::LeanObject,
    mut v_x_1964_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1965_: u8 = 0;
    let mut v_r_1966_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1965_ = l_Std_Async_System_instDecidableEqCPUTimes_decEq(v_x_1963_, v_x_1964_);
    crate::leanh::lean_dec_ref(v_x_1964_);
    crate::leanh::lean_dec_ref(v_x_1963_);
    v_r_1966_ = crate::leanh::lean_box((v_res_1965_) as usize);
    return v_r_1966_;
}
pub unsafe fn l_Std_Async_System_instDecidableEqCPUTimes(
    mut v_x_1967_: *mut crate::leanh::LeanObject,
    mut v_x_1968_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_1969_: u8 = 0;
    v___x_1969_ = l_Std_Async_System_instDecidableEqCPUTimes_decEq(v_x_1967_, v_x_1968_);
    return v___x_1969_;
}
pub unsafe fn l_Std_Async_System_instDecidableEqCPUTimes___boxed(
    mut v_x_1970_: *mut crate::leanh::LeanObject,
    mut v_x_1971_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1972_: u8 = 0;
    let mut v_r_1973_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1972_ = l_Std_Async_System_instDecidableEqCPUTimes(v_x_1970_, v_x_1971_);
    crate::leanh::lean_dec_ref(v_x_1971_);
    crate::leanh::lean_dec_ref(v_x_1970_);
    v_r_1973_ = crate::leanh::lean_box((v_res_1972_) as usize);
    return v_r_1973_;
}
pub unsafe fn _init_l_Std_Async_System_instReprCPUTimes_repr___redArg___closed__8()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1989_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1990_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1989_ = crate::leanh::lean_unsigned_to_nat(14);
    v___x_1990_ = lean_nat_to_int(v___x_1989_);
    return v___x_1990_;
}
pub unsafe fn _init_l_Std_Async_System_instReprCPUTimes_repr___redArg___closed__13()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1997_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1998_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1997_ = crate::leanh::lean_unsigned_to_nat(17);
    v___x_1998_ = lean_nat_to_int(v___x_1997_);
    return v___x_1998_;
}
pub unsafe fn l_Std_Async_System_instReprCPUTimes_repr___redArg(
    mut v_x_1999_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_userTime_2000_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_niceTime_2001_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_systemTime_2002_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_idleTime_2003_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_interruptTime_2004_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2005_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2006_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2007_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2008_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2009_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2010_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2011_: u8 = 0;
    let mut v___x_2012_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2013_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2014_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2015_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2016_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2017_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2018_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2019_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2020_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2021_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2022_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2023_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2024_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2025_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2026_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2027_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2028_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2029_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2030_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2031_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2032_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2033_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2034_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2035_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2036_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2037_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2038_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2039_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2040_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2041_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2042_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2043_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2044_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2045_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2046_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2047_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2048_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2049_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2050_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2051_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2052_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2053_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2054_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2055_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2056_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2057_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2058_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2059_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2060_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_userTime_2000_ = crate::leanh::lean_ctor_get(v_x_1999_, 0);
    v_niceTime_2001_ = crate::leanh::lean_ctor_get(v_x_1999_, 1);
    v_systemTime_2002_ = crate::leanh::lean_ctor_get(v_x_1999_, 2);
    v_idleTime_2003_ = crate::leanh::lean_ctor_get(v_x_1999_, 3);
    v_interruptTime_2004_ = crate::leanh::lean_ctor_get(v_x_1999_, 4);
    v___x_2005_ = l_Std_Async_System_instReprSystemUser_repr___redArg___closed__5;
    v___x_2006_ = l_Std_Async_System_instReprCPUTimes_repr___redArg___closed__3;
    v___x_2007_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Async_System_instReprSystemUser_repr___redArg___closed__7),
        core::ptr::addr_of_mut!(
            l_Std_Async_System_instReprSystemUser_repr___redArg___closed__7_once
        ),
        _init_l_Std_Async_System_instReprSystemUser_repr___redArg___closed__7,
    );
    v___x_2008_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_2009_ = l_Std_Time_Millisecond_instReprOrdinal___lam__0(v_userTime_2000_, v___x_2008_);
    v___x_2010_ = crate::leanh::lean_alloc_ctor(4, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2010_, 0, v___x_2007_);
    crate::leanh::lean_ctor_set(v___x_2010_, 1, v___x_2009_);
    v___x_2011_ = 0;
    v___x_2012_ = crate::leanh::lean_alloc_ctor(6, 1, (1) as u32);
    crate::leanh::lean_ctor_set(v___x_2012_, 0, v___x_2010_);
    crate::leanh::lean_ctor_set_uint8(
        v___x_2012_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
        v___x_2011_,
    );
    v___x_2013_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2013_, 0, v___x_2006_);
    crate::leanh::lean_ctor_set(v___x_2013_, 1, v___x_2012_);
    v___x_2014_ = l_Std_Async_System_instReprSystemUser_repr___redArg___closed__9;
    v___x_2015_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2015_, 0, v___x_2013_);
    crate::leanh::lean_ctor_set(v___x_2015_, 1, v___x_2014_);
    v___x_2016_ = crate::leanh::lean_box(1);
    v___x_2017_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2017_, 0, v___x_2015_);
    crate::leanh::lean_ctor_set(v___x_2017_, 1, v___x_2016_);
    v___x_2018_ = l_Std_Async_System_instReprCPUTimes_repr___redArg___closed__5;
    v___x_2019_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2019_, 0, v___x_2017_);
    crate::leanh::lean_ctor_set(v___x_2019_, 1, v___x_2018_);
    v___x_2020_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2020_, 0, v___x_2019_);
    crate::leanh::lean_ctor_set(v___x_2020_, 1, v___x_2005_);
    v___x_2021_ = l_Std_Time_Millisecond_instReprOrdinal___lam__0(v_niceTime_2001_, v___x_2008_);
    v___x_2022_ = crate::leanh::lean_alloc_ctor(4, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2022_, 0, v___x_2007_);
    crate::leanh::lean_ctor_set(v___x_2022_, 1, v___x_2021_);
    v___x_2023_ = crate::leanh::lean_alloc_ctor(6, 1, (1) as u32);
    crate::leanh::lean_ctor_set(v___x_2023_, 0, v___x_2022_);
    crate::leanh::lean_ctor_set_uint8(
        v___x_2023_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
        v___x_2011_,
    );
    v___x_2024_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2024_, 0, v___x_2020_);
    crate::leanh::lean_ctor_set(v___x_2024_, 1, v___x_2023_);
    v___x_2025_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2025_, 0, v___x_2024_);
    crate::leanh::lean_ctor_set(v___x_2025_, 1, v___x_2014_);
    v___x_2026_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2026_, 0, v___x_2025_);
    crate::leanh::lean_ctor_set(v___x_2026_, 1, v___x_2016_);
    v___x_2027_ = l_Std_Async_System_instReprCPUTimes_repr___redArg___closed__7;
    v___x_2028_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2028_, 0, v___x_2026_);
    crate::leanh::lean_ctor_set(v___x_2028_, 1, v___x_2027_);
    v___x_2029_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2029_, 0, v___x_2028_);
    crate::leanh::lean_ctor_set(v___x_2029_, 1, v___x_2005_);
    v___x_2030_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Async_System_instReprCPUTimes_repr___redArg___closed__8),
        core::ptr::addr_of_mut!(l_Std_Async_System_instReprCPUTimes_repr___redArg___closed__8_once),
        _init_l_Std_Async_System_instReprCPUTimes_repr___redArg___closed__8,
    );
    v___x_2031_ = l_Std_Time_Millisecond_instReprOrdinal___lam__0(v_systemTime_2002_, v___x_2008_);
    v___x_2032_ = crate::leanh::lean_alloc_ctor(4, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2032_, 0, v___x_2030_);
    crate::leanh::lean_ctor_set(v___x_2032_, 1, v___x_2031_);
    v___x_2033_ = crate::leanh::lean_alloc_ctor(6, 1, (1) as u32);
    crate::leanh::lean_ctor_set(v___x_2033_, 0, v___x_2032_);
    crate::leanh::lean_ctor_set_uint8(
        v___x_2033_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
        v___x_2011_,
    );
    v___x_2034_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2034_, 0, v___x_2029_);
    crate::leanh::lean_ctor_set(v___x_2034_, 1, v___x_2033_);
    v___x_2035_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2035_, 0, v___x_2034_);
    crate::leanh::lean_ctor_set(v___x_2035_, 1, v___x_2014_);
    v___x_2036_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2036_, 0, v___x_2035_);
    crate::leanh::lean_ctor_set(v___x_2036_, 1, v___x_2016_);
    v___x_2037_ = l_Std_Async_System_instReprCPUTimes_repr___redArg___closed__10;
    v___x_2038_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2038_, 0, v___x_2036_);
    crate::leanh::lean_ctor_set(v___x_2038_, 1, v___x_2037_);
    v___x_2039_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2039_, 0, v___x_2038_);
    crate::leanh::lean_ctor_set(v___x_2039_, 1, v___x_2005_);
    v___x_2040_ = l_Std_Time_Millisecond_instReprOrdinal___lam__0(v_idleTime_2003_, v___x_2008_);
    v___x_2041_ = crate::leanh::lean_alloc_ctor(4, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2041_, 0, v___x_2007_);
    crate::leanh::lean_ctor_set(v___x_2041_, 1, v___x_2040_);
    v___x_2042_ = crate::leanh::lean_alloc_ctor(6, 1, (1) as u32);
    crate::leanh::lean_ctor_set(v___x_2042_, 0, v___x_2041_);
    crate::leanh::lean_ctor_set_uint8(
        v___x_2042_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
        v___x_2011_,
    );
    v___x_2043_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2043_, 0, v___x_2039_);
    crate::leanh::lean_ctor_set(v___x_2043_, 1, v___x_2042_);
    v___x_2044_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2044_, 0, v___x_2043_);
    crate::leanh::lean_ctor_set(v___x_2044_, 1, v___x_2014_);
    v___x_2045_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2045_, 0, v___x_2044_);
    crate::leanh::lean_ctor_set(v___x_2045_, 1, v___x_2016_);
    v___x_2046_ = l_Std_Async_System_instReprCPUTimes_repr___redArg___closed__12;
    v___x_2047_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2047_, 0, v___x_2045_);
    crate::leanh::lean_ctor_set(v___x_2047_, 1, v___x_2046_);
    v___x_2048_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2048_, 0, v___x_2047_);
    crate::leanh::lean_ctor_set(v___x_2048_, 1, v___x_2005_);
    v___x_2049_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Async_System_instReprCPUTimes_repr___redArg___closed__13),
        core::ptr::addr_of_mut!(
            l_Std_Async_System_instReprCPUTimes_repr___redArg___closed__13_once
        ),
        _init_l_Std_Async_System_instReprCPUTimes_repr___redArg___closed__13,
    );
    v___x_2050_ =
        l_Std_Time_Millisecond_instReprOrdinal___lam__0(v_interruptTime_2004_, v___x_2008_);
    v___x_2051_ = crate::leanh::lean_alloc_ctor(4, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2051_, 0, v___x_2049_);
    crate::leanh::lean_ctor_set(v___x_2051_, 1, v___x_2050_);
    v___x_2052_ = crate::leanh::lean_alloc_ctor(6, 1, (1) as u32);
    crate::leanh::lean_ctor_set(v___x_2052_, 0, v___x_2051_);
    crate::leanh::lean_ctor_set_uint8(
        v___x_2052_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
        v___x_2011_,
    );
    v___x_2053_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2053_, 0, v___x_2048_);
    crate::leanh::lean_ctor_set(v___x_2053_, 1, v___x_2052_);
    v___x_2054_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Async_System_instReprSystemUser_repr___redArg___closed__23),
        core::ptr::addr_of_mut!(
            l_Std_Async_System_instReprSystemUser_repr___redArg___closed__23_once
        ),
        _init_l_Std_Async_System_instReprSystemUser_repr___redArg___closed__23,
    );
    v___x_2055_ = l_Std_Async_System_instReprSystemUser_repr___redArg___closed__24;
    v___x_2056_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2056_, 0, v___x_2055_);
    crate::leanh::lean_ctor_set(v___x_2056_, 1, v___x_2053_);
    v___x_2057_ = l_Std_Async_System_instReprSystemUser_repr___redArg___closed__25;
    v___x_2058_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2058_, 0, v___x_2056_);
    crate::leanh::lean_ctor_set(v___x_2058_, 1, v___x_2057_);
    v___x_2059_ = crate::leanh::lean_alloc_ctor(4, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2059_, 0, v___x_2054_);
    crate::leanh::lean_ctor_set(v___x_2059_, 1, v___x_2058_);
    v___x_2060_ = crate::leanh::lean_alloc_ctor(6, 1, (1) as u32);
    crate::leanh::lean_ctor_set(v___x_2060_, 0, v___x_2059_);
    crate::leanh::lean_ctor_set_uint8(
        v___x_2060_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
        v___x_2011_,
    );
    return v___x_2060_;
}
pub unsafe fn l_Std_Async_System_instReprCPUTimes_repr___redArg___boxed(
    mut v_x_2061_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2062_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2062_ = l_Std_Async_System_instReprCPUTimes_repr___redArg(v_x_2061_);
    crate::leanh::lean_dec_ref(v_x_2061_);
    return v_res_2062_;
}
pub unsafe fn l_Std_Async_System_instReprCPUTimes_repr(
    mut v_x_2063_: *mut crate::leanh::LeanObject,
    mut v_prec_2064_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2065_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2065_ = l_Std_Async_System_instReprCPUTimes_repr___redArg(v_x_2063_);
    return v___x_2065_;
}
pub unsafe fn l_Std_Async_System_instReprCPUTimes_repr___boxed(
    mut v_x_2066_: *mut crate::leanh::LeanObject,
    mut v_prec_2067_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2068_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2068_ = l_Std_Async_System_instReprCPUTimes_repr(v_x_2066_, v_prec_2067_);
    crate::leanh::lean_dec(v_prec_2067_);
    crate::leanh::lean_dec_ref(v_x_2066_);
    return v_res_2068_;
}
pub unsafe fn _init_l_Std_Async_System_instInhabitedCPUInfo_default___closed__0()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2071_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2072_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2073_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2074_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2071_ = l_Std_Async_System_instInhabitedCPUTimes_default;
    v___x_2072_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_2073_ = l_Std_Async_System_instInhabitedSystemUser_default___closed__0;
    v___x_2074_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2074_, 0, v___x_2073_);
    crate::leanh::lean_ctor_set(v___x_2074_, 1, v___x_2072_);
    crate::leanh::lean_ctor_set(v___x_2074_, 2, v___x_2071_);
    return v___x_2074_;
}
pub unsafe fn _init_l_Std_Async_System_instInhabitedCPUInfo_default()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2075_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2075_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Async_System_instInhabitedCPUInfo_default___closed__0),
        core::ptr::addr_of_mut!(l_Std_Async_System_instInhabitedCPUInfo_default___closed__0_once),
        _init_l_Std_Async_System_instInhabitedCPUInfo_default___closed__0,
    );
    return v___x_2075_;
}
pub unsafe fn _init_l_Std_Async_System_instInhabitedCPUInfo() -> *mut crate::leanh::LeanObject {
    let mut v___x_2076_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2076_ = l_Std_Async_System_instInhabitedCPUInfo_default;
    return v___x_2076_;
}
pub unsafe fn l_Std_Async_System_instDecidableEqCPUInfo_decEq(
    mut v_x_2077_: *mut crate::leanh::LeanObject,
    mut v_x_2078_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v_model_2079_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_speed_2080_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_times_2081_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_model_2082_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_speed_2083_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_times_2084_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2085_: u8 = 0;
    v_model_2079_ = crate::leanh::lean_ctor_get(v_x_2077_, 0);
    v_speed_2080_ = crate::leanh::lean_ctor_get(v_x_2077_, 1);
    v_times_2081_ = crate::leanh::lean_ctor_get(v_x_2077_, 2);
    v_model_2082_ = crate::leanh::lean_ctor_get(v_x_2078_, 0);
    v_speed_2083_ = crate::leanh::lean_ctor_get(v_x_2078_, 1);
    v_times_2084_ = crate::leanh::lean_ctor_get(v_x_2078_, 2);
    v___x_2085_ = lean_string_dec_eq(v_model_2079_, v_model_2082_);
    if v___x_2085_ == 0 {
        return v___x_2085_;
    } else {
        let mut v___x_2086_: u8 = 0;
        v___x_2086_ = lean_nat_dec_eq(v_speed_2080_, v_speed_2083_);
        if v___x_2086_ == 0 {
            return v___x_2086_;
        } else {
            let mut v___x_2087_: u8 = 0;
            v___x_2087_ =
                l_Std_Async_System_instDecidableEqCPUTimes_decEq(v_times_2081_, v_times_2084_);
            return v___x_2087_;
        }
    }
}
pub unsafe fn l_Std_Async_System_instDecidableEqCPUInfo_decEq___boxed(
    mut v_x_2088_: *mut crate::leanh::LeanObject,
    mut v_x_2089_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2090_: u8 = 0;
    let mut v_r_2091_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2090_ = l_Std_Async_System_instDecidableEqCPUInfo_decEq(v_x_2088_, v_x_2089_);
    crate::leanh::lean_dec_ref(v_x_2089_);
    crate::leanh::lean_dec_ref(v_x_2088_);
    v_r_2091_ = crate::leanh::lean_box((v_res_2090_) as usize);
    return v_r_2091_;
}
pub unsafe fn l_Std_Async_System_instDecidableEqCPUInfo(
    mut v_x_2092_: *mut crate::leanh::LeanObject,
    mut v_x_2093_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_2094_: u8 = 0;
    v___x_2094_ = l_Std_Async_System_instDecidableEqCPUInfo_decEq(v_x_2092_, v_x_2093_);
    return v___x_2094_;
}
pub unsafe fn l_Std_Async_System_instDecidableEqCPUInfo___boxed(
    mut v_x_2095_: *mut crate::leanh::LeanObject,
    mut v_x_2096_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2097_: u8 = 0;
    let mut v_r_2098_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2097_ = l_Std_Async_System_instDecidableEqCPUInfo(v_x_2095_, v_x_2096_);
    crate::leanh::lean_dec_ref(v_x_2096_);
    crate::leanh::lean_dec_ref(v_x_2095_);
    v_r_2098_ = crate::leanh::lean_box((v_res_2097_) as usize);
    return v_r_2098_;
}
pub unsafe fn l_Std_Async_System_instReprCPUInfo_repr___redArg(
    mut v_x_2114_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_model_2115_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_speed_2116_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_times_2117_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2118_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2119_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2120_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2121_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2122_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2123_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2124_: u8 = 0;
    let mut v___x_2125_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2126_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2127_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2128_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2129_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2130_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2131_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2132_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2133_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2134_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2135_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2136_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2137_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2138_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2139_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2140_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2141_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2142_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2143_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2144_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2145_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2146_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2147_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2148_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2149_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2150_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2151_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2152_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2153_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2154_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_model_2115_ = crate::leanh::lean_ctor_get(v_x_2114_, 0);
    crate::leanh::lean_inc_ref(v_model_2115_);
    v_speed_2116_ = crate::leanh::lean_ctor_get(v_x_2114_, 1);
    crate::leanh::lean_inc(v_speed_2116_);
    v_times_2117_ = crate::leanh::lean_ctor_get(v_x_2114_, 2);
    crate::leanh::lean_inc_ref(v_times_2117_);
    crate::leanh::lean_dec_ref(v_x_2114_);
    v___x_2118_ = l_Std_Async_System_instReprSystemUser_repr___redArg___closed__5;
    v___x_2119_ = l_Std_Async_System_instReprCPUInfo_repr___redArg___closed__3;
    v___x_2120_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Async_System_instReprSystemUser_repr___redArg___closed__18),
        core::ptr::addr_of_mut!(
            l_Std_Async_System_instReprSystemUser_repr___redArg___closed__18_once
        ),
        _init_l_Std_Async_System_instReprSystemUser_repr___redArg___closed__18,
    );
    v___x_2121_ = l_String_quote(v_model_2115_);
    v___x_2122_ = crate::leanh::lean_alloc_ctor(3, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2122_, 0, v___x_2121_);
    v___x_2123_ = crate::leanh::lean_alloc_ctor(4, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2123_, 0, v___x_2120_);
    crate::leanh::lean_ctor_set(v___x_2123_, 1, v___x_2122_);
    v___x_2124_ = 0;
    v___x_2125_ = crate::leanh::lean_alloc_ctor(6, 1, (1) as u32);
    crate::leanh::lean_ctor_set(v___x_2125_, 0, v___x_2123_);
    crate::leanh::lean_ctor_set_uint8(
        v___x_2125_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
        v___x_2124_,
    );
    v___x_2126_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2126_, 0, v___x_2119_);
    crate::leanh::lean_ctor_set(v___x_2126_, 1, v___x_2125_);
    v___x_2127_ = l_Std_Async_System_instReprSystemUser_repr___redArg___closed__9;
    v___x_2128_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2128_, 0, v___x_2126_);
    crate::leanh::lean_ctor_set(v___x_2128_, 1, v___x_2127_);
    v___x_2129_ = crate::leanh::lean_box(1);
    v___x_2130_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2130_, 0, v___x_2128_);
    crate::leanh::lean_ctor_set(v___x_2130_, 1, v___x_2129_);
    v___x_2131_ = l_Std_Async_System_instReprCPUInfo_repr___redArg___closed__5;
    v___x_2132_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2132_, 0, v___x_2130_);
    crate::leanh::lean_ctor_set(v___x_2132_, 1, v___x_2131_);
    v___x_2133_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2133_, 0, v___x_2132_);
    crate::leanh::lean_ctor_set(v___x_2133_, 1, v___x_2118_);
    v___x_2134_ = l_Nat_reprFast(v_speed_2116_);
    v___x_2135_ = crate::leanh::lean_alloc_ctor(3, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2135_, 0, v___x_2134_);
    v___x_2136_ = crate::leanh::lean_alloc_ctor(4, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2136_, 0, v___x_2120_);
    crate::leanh::lean_ctor_set(v___x_2136_, 1, v___x_2135_);
    v___x_2137_ = crate::leanh::lean_alloc_ctor(6, 1, (1) as u32);
    crate::leanh::lean_ctor_set(v___x_2137_, 0, v___x_2136_);
    crate::leanh::lean_ctor_set_uint8(
        v___x_2137_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
        v___x_2124_,
    );
    v___x_2138_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2138_, 0, v___x_2133_);
    crate::leanh::lean_ctor_set(v___x_2138_, 1, v___x_2137_);
    v___x_2139_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2139_, 0, v___x_2138_);
    crate::leanh::lean_ctor_set(v___x_2139_, 1, v___x_2127_);
    v___x_2140_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2140_, 0, v___x_2139_);
    crate::leanh::lean_ctor_set(v___x_2140_, 1, v___x_2129_);
    v___x_2141_ = l_Std_Async_System_instReprCPUInfo_repr___redArg___closed__7;
    v___x_2142_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2142_, 0, v___x_2140_);
    crate::leanh::lean_ctor_set(v___x_2142_, 1, v___x_2141_);
    v___x_2143_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2143_, 0, v___x_2142_);
    crate::leanh::lean_ctor_set(v___x_2143_, 1, v___x_2118_);
    v___x_2144_ = l_Std_Async_System_instReprCPUTimes_repr___redArg(v_times_2117_);
    crate::leanh::lean_dec_ref(v_times_2117_);
    v___x_2145_ = crate::leanh::lean_alloc_ctor(4, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2145_, 0, v___x_2120_);
    crate::leanh::lean_ctor_set(v___x_2145_, 1, v___x_2144_);
    v___x_2146_ = crate::leanh::lean_alloc_ctor(6, 1, (1) as u32);
    crate::leanh::lean_ctor_set(v___x_2146_, 0, v___x_2145_);
    crate::leanh::lean_ctor_set_uint8(
        v___x_2146_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
        v___x_2124_,
    );
    v___x_2147_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2147_, 0, v___x_2143_);
    crate::leanh::lean_ctor_set(v___x_2147_, 1, v___x_2146_);
    v___x_2148_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Async_System_instReprSystemUser_repr___redArg___closed__23),
        core::ptr::addr_of_mut!(
            l_Std_Async_System_instReprSystemUser_repr___redArg___closed__23_once
        ),
        _init_l_Std_Async_System_instReprSystemUser_repr___redArg___closed__23,
    );
    v___x_2149_ = l_Std_Async_System_instReprSystemUser_repr___redArg___closed__24;
    v___x_2150_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2150_, 0, v___x_2149_);
    crate::leanh::lean_ctor_set(v___x_2150_, 1, v___x_2147_);
    v___x_2151_ = l_Std_Async_System_instReprSystemUser_repr___redArg___closed__25;
    v___x_2152_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2152_, 0, v___x_2150_);
    crate::leanh::lean_ctor_set(v___x_2152_, 1, v___x_2151_);
    v___x_2153_ = crate::leanh::lean_alloc_ctor(4, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2153_, 0, v___x_2148_);
    crate::leanh::lean_ctor_set(v___x_2153_, 1, v___x_2152_);
    v___x_2154_ = crate::leanh::lean_alloc_ctor(6, 1, (1) as u32);
    crate::leanh::lean_ctor_set(v___x_2154_, 0, v___x_2153_);
    crate::leanh::lean_ctor_set_uint8(
        v___x_2154_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
        v___x_2124_,
    );
    return v___x_2154_;
}
pub unsafe fn l_Std_Async_System_instReprCPUInfo_repr(
    mut v_x_2155_: *mut crate::leanh::LeanObject,
    mut v_prec_2156_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2157_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2157_ = l_Std_Async_System_instReprCPUInfo_repr___redArg(v_x_2155_);
    return v___x_2157_;
}
pub unsafe fn l_Std_Async_System_instReprCPUInfo_repr___boxed(
    mut v_x_2158_: *mut crate::leanh::LeanObject,
    mut v_prec_2159_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2160_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2160_ = l_Std_Async_System_instReprCPUInfo_repr(v_x_2158_, v_prec_2159_);
    crate::leanh::lean_dec(v_prec_2159_);
    return v_res_2160_;
}
pub unsafe fn _init_l_Std_Async_System_instReprOSInfo_repr___redArg___closed__4()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2172_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2173_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2172_ = crate::leanh::lean_unsigned_to_nat(8);
    v___x_2173_ = lean_nat_to_int(v___x_2172_);
    return v___x_2173_;
}
pub unsafe fn l_Std_Async_System_instReprOSInfo_repr___redArg(
    mut v_x_2183_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_name_2184_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_release_2185_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_version_2186_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_machine_2187_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2188_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2189_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2190_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2191_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2192_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2193_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2194_: u8 = 0;
    let mut v___x_2195_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2196_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2197_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2198_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2199_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2200_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2201_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2202_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2203_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2204_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2205_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2206_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2207_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2208_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2209_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2210_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2211_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2212_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2213_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2214_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2215_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2216_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2217_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2218_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2219_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2220_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2221_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2222_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2223_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2224_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2225_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2226_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2227_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2228_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2229_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2230_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2231_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2232_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2233_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2234_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2235_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2236_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_name_2184_ = crate::leanh::lean_ctor_get(v_x_2183_, 0);
    crate::leanh::lean_inc_ref(v_name_2184_);
    v_release_2185_ = crate::leanh::lean_ctor_get(v_x_2183_, 1);
    crate::leanh::lean_inc_ref(v_release_2185_);
    v_version_2186_ = crate::leanh::lean_ctor_get(v_x_2183_, 2);
    crate::leanh::lean_inc_ref(v_version_2186_);
    v_machine_2187_ = crate::leanh::lean_ctor_get(v_x_2183_, 3);
    crate::leanh::lean_inc_ref(v_machine_2187_);
    crate::leanh::lean_dec_ref(v_x_2183_);
    v___x_2188_ = l_Std_Async_System_instReprSystemUser_repr___redArg___closed__5;
    v___x_2189_ = l_Std_Async_System_instReprOSInfo_repr___redArg___closed__3;
    v___x_2190_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Async_System_instReprOSInfo_repr___redArg___closed__4),
        core::ptr::addr_of_mut!(l_Std_Async_System_instReprOSInfo_repr___redArg___closed__4_once),
        _init_l_Std_Async_System_instReprOSInfo_repr___redArg___closed__4,
    );
    v___x_2191_ = l_String_quote(v_name_2184_);
    v___x_2192_ = crate::leanh::lean_alloc_ctor(3, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2192_, 0, v___x_2191_);
    v___x_2193_ = crate::leanh::lean_alloc_ctor(4, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2193_, 0, v___x_2190_);
    crate::leanh::lean_ctor_set(v___x_2193_, 1, v___x_2192_);
    v___x_2194_ = 0;
    v___x_2195_ = crate::leanh::lean_alloc_ctor(6, 1, (1) as u32);
    crate::leanh::lean_ctor_set(v___x_2195_, 0, v___x_2193_);
    crate::leanh::lean_ctor_set_uint8(
        v___x_2195_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
        v___x_2194_,
    );
    v___x_2196_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2196_, 0, v___x_2189_);
    crate::leanh::lean_ctor_set(v___x_2196_, 1, v___x_2195_);
    v___x_2197_ = l_Std_Async_System_instReprSystemUser_repr___redArg___closed__9;
    v___x_2198_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2198_, 0, v___x_2196_);
    crate::leanh::lean_ctor_set(v___x_2198_, 1, v___x_2197_);
    v___x_2199_ = crate::leanh::lean_box(1);
    v___x_2200_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2200_, 0, v___x_2198_);
    crate::leanh::lean_ctor_set(v___x_2200_, 1, v___x_2199_);
    v___x_2201_ = l_Std_Async_System_instReprOSInfo_repr___redArg___closed__6;
    v___x_2202_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2202_, 0, v___x_2200_);
    crate::leanh::lean_ctor_set(v___x_2202_, 1, v___x_2201_);
    v___x_2203_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2203_, 0, v___x_2202_);
    crate::leanh::lean_ctor_set(v___x_2203_, 1, v___x_2188_);
    v___x_2204_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Async_System_instReprSystemUser_repr___redArg___closed__15),
        core::ptr::addr_of_mut!(
            l_Std_Async_System_instReprSystemUser_repr___redArg___closed__15_once
        ),
        _init_l_Std_Async_System_instReprSystemUser_repr___redArg___closed__15,
    );
    v___x_2205_ = l_String_quote(v_release_2185_);
    v___x_2206_ = crate::leanh::lean_alloc_ctor(3, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2206_, 0, v___x_2205_);
    v___x_2207_ = crate::leanh::lean_alloc_ctor(4, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2207_, 0, v___x_2204_);
    crate::leanh::lean_ctor_set(v___x_2207_, 1, v___x_2206_);
    v___x_2208_ = crate::leanh::lean_alloc_ctor(6, 1, (1) as u32);
    crate::leanh::lean_ctor_set(v___x_2208_, 0, v___x_2207_);
    crate::leanh::lean_ctor_set_uint8(
        v___x_2208_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
        v___x_2194_,
    );
    v___x_2209_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2209_, 0, v___x_2203_);
    crate::leanh::lean_ctor_set(v___x_2209_, 1, v___x_2208_);
    v___x_2210_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2210_, 0, v___x_2209_);
    crate::leanh::lean_ctor_set(v___x_2210_, 1, v___x_2197_);
    v___x_2211_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2211_, 0, v___x_2210_);
    crate::leanh::lean_ctor_set(v___x_2211_, 1, v___x_2199_);
    v___x_2212_ = l_Std_Async_System_instReprOSInfo_repr___redArg___closed__8;
    v___x_2213_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2213_, 0, v___x_2211_);
    crate::leanh::lean_ctor_set(v___x_2213_, 1, v___x_2212_);
    v___x_2214_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2214_, 0, v___x_2213_);
    crate::leanh::lean_ctor_set(v___x_2214_, 1, v___x_2188_);
    v___x_2215_ = l_String_quote(v_version_2186_);
    v___x_2216_ = crate::leanh::lean_alloc_ctor(3, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2216_, 0, v___x_2215_);
    v___x_2217_ = crate::leanh::lean_alloc_ctor(4, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2217_, 0, v___x_2204_);
    crate::leanh::lean_ctor_set(v___x_2217_, 1, v___x_2216_);
    v___x_2218_ = crate::leanh::lean_alloc_ctor(6, 1, (1) as u32);
    crate::leanh::lean_ctor_set(v___x_2218_, 0, v___x_2217_);
    crate::leanh::lean_ctor_set_uint8(
        v___x_2218_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
        v___x_2194_,
    );
    v___x_2219_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2219_, 0, v___x_2214_);
    crate::leanh::lean_ctor_set(v___x_2219_, 1, v___x_2218_);
    v___x_2220_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2220_, 0, v___x_2219_);
    crate::leanh::lean_ctor_set(v___x_2220_, 1, v___x_2197_);
    v___x_2221_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2221_, 0, v___x_2220_);
    crate::leanh::lean_ctor_set(v___x_2221_, 1, v___x_2199_);
    v___x_2222_ = l_Std_Async_System_instReprOSInfo_repr___redArg___closed__10;
    v___x_2223_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2223_, 0, v___x_2221_);
    crate::leanh::lean_ctor_set(v___x_2223_, 1, v___x_2222_);
    v___x_2224_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2224_, 0, v___x_2223_);
    crate::leanh::lean_ctor_set(v___x_2224_, 1, v___x_2188_);
    v___x_2225_ = l_String_quote(v_machine_2187_);
    v___x_2226_ = crate::leanh::lean_alloc_ctor(3, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2226_, 0, v___x_2225_);
    v___x_2227_ = crate::leanh::lean_alloc_ctor(4, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2227_, 0, v___x_2204_);
    crate::leanh::lean_ctor_set(v___x_2227_, 1, v___x_2226_);
    v___x_2228_ = crate::leanh::lean_alloc_ctor(6, 1, (1) as u32);
    crate::leanh::lean_ctor_set(v___x_2228_, 0, v___x_2227_);
    crate::leanh::lean_ctor_set_uint8(
        v___x_2228_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
        v___x_2194_,
    );
    v___x_2229_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2229_, 0, v___x_2224_);
    crate::leanh::lean_ctor_set(v___x_2229_, 1, v___x_2228_);
    v___x_2230_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Async_System_instReprSystemUser_repr___redArg___closed__23),
        core::ptr::addr_of_mut!(
            l_Std_Async_System_instReprSystemUser_repr___redArg___closed__23_once
        ),
        _init_l_Std_Async_System_instReprSystemUser_repr___redArg___closed__23,
    );
    v___x_2231_ = l_Std_Async_System_instReprSystemUser_repr___redArg___closed__24;
    v___x_2232_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2232_, 0, v___x_2231_);
    crate::leanh::lean_ctor_set(v___x_2232_, 1, v___x_2229_);
    v___x_2233_ = l_Std_Async_System_instReprSystemUser_repr___redArg___closed__25;
    v___x_2234_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2234_, 0, v___x_2232_);
    crate::leanh::lean_ctor_set(v___x_2234_, 1, v___x_2233_);
    v___x_2235_ = crate::leanh::lean_alloc_ctor(4, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2235_, 0, v___x_2230_);
    crate::leanh::lean_ctor_set(v___x_2235_, 1, v___x_2234_);
    v___x_2236_ = crate::leanh::lean_alloc_ctor(6, 1, (1) as u32);
    crate::leanh::lean_ctor_set(v___x_2236_, 0, v___x_2235_);
    crate::leanh::lean_ctor_set_uint8(
        v___x_2236_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
        v___x_2194_,
    );
    return v___x_2236_;
}
pub unsafe fn l_Std_Async_System_instReprOSInfo_repr(
    mut v_x_2237_: *mut crate::leanh::LeanObject,
    mut v_prec_2238_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2239_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2239_ = l_Std_Async_System_instReprOSInfo_repr___redArg(v_x_2237_);
    return v___x_2239_;
}
pub unsafe fn l_Std_Async_System_instReprOSInfo_repr___boxed(
    mut v_x_2240_: *mut crate::leanh::LeanObject,
    mut v_prec_2241_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2242_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2242_ = l_Std_Async_System_instReprOSInfo_repr(v_x_2240_, v_prec_2241_);
    crate::leanh::lean_dec(v_prec_2241_);
    return v_res_2242_;
}
pub unsafe fn _init_l_Std_Async_System_instInhabitedEnvironment_default___closed__0()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2249_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2250_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2251_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2249_ = crate::leanh::lean_box(0);
    v___x_2250_ = crate::leanh::lean_unsigned_to_nat(16);
    v___x_2251_ = lean_mk_array(v___x_2250_, v___x_2249_);
    return v___x_2251_;
}
pub unsafe fn _init_l_Std_Async_System_instInhabitedEnvironment_default___closed__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2252_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2253_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2254_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2252_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Async_System_instInhabitedEnvironment_default___closed__0),
        core::ptr::addr_of_mut!(
            l_Std_Async_System_instInhabitedEnvironment_default___closed__0_once
        ),
        _init_l_Std_Async_System_instInhabitedEnvironment_default___closed__0,
    );
    v___x_2253_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_2254_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2254_, 0, v___x_2253_);
    crate::leanh::lean_ctor_set(v___x_2254_, 1, v___x_2252_);
    return v___x_2254_;
}
pub unsafe fn _init_l_Std_Async_System_instInhabitedEnvironment_default()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2255_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2255_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Async_System_instInhabitedEnvironment_default___closed__1),
        core::ptr::addr_of_mut!(
            l_Std_Async_System_instInhabitedEnvironment_default___closed__1_once
        ),
        _init_l_Std_Async_System_instInhabitedEnvironment_default___closed__1,
    );
    return v___x_2255_;
}
pub unsafe fn _init_l_Std_Async_System_instInhabitedEnvironment() -> *mut crate::leanh::LeanObject {
    let mut v___x_2256_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2256_ = l_Std_Async_System_instInhabitedEnvironment_default;
    return v___x_2256_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_foldrM___at___00Std_Async_System_instReprEnvironment_repr_spec__1(
    mut v_x_2257_: *mut crate::leanh::LeanObject,
    mut v_x_2258_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_2258_) == 0 {
        crate::leanh::lean_inc(v_x_2257_);
        return v_x_2257_;
    } else {
        let mut v_key_2259_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_value_2260_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_tail_2261_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2262_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2263_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2264_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_key_2259_ = crate::leanh::lean_ctor_get(v_x_2258_, 0);
        v_value_2260_ = crate::leanh::lean_ctor_get(v_x_2258_, 1);
        v_tail_2261_ = crate::leanh::lean_ctor_get(v_x_2258_, 2);
        v___x_2262_ = l_Std_DHashMap_Internal_AssocList_foldrM___at___00Std_Async_System_instReprEnvironment_repr_spec__1(v_x_2257_, v_tail_2261_);
        crate::leanh::lean_inc(v_value_2260_);
        crate::leanh::lean_inc(v_key_2259_);
        v___x_2263_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_2263_, 0, v_key_2259_);
        crate::leanh::lean_ctor_set(v___x_2263_, 1, v_value_2260_);
        v___x_2264_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_2264_, 0, v___x_2263_);
        crate::leanh::lean_ctor_set(v___x_2264_, 1, v___x_2262_);
        return v___x_2264_;
    }
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_foldrM___at___00Std_Async_System_instReprEnvironment_repr_spec__1___boxed(
    mut v_x_2265_: *mut crate::leanh::LeanObject,
    mut v_x_2266_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2267_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2267_ = l_Std_DHashMap_Internal_AssocList_foldrM___at___00Std_Async_System_instReprEnvironment_repr_spec__1(v_x_2265_, v_x_2266_);
    crate::leanh::lean_dec(v_x_2266_);
    crate::leanh::lean_dec(v_x_2265_);
    return v_res_2267_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Std_Async_System_instReprEnvironment_repr_spec__2(
    mut v_as_2268_: *mut crate::leanh::LeanObject,
    mut v_i_2269_: usize,
    mut v_stop_2270_: usize,
    mut v_b_2271_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2272_: u8 = 0;
    let mut v___x_2273_: usize = 0;
    let mut v___x_2274_: usize = 0;
    let mut v___x_2275_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2276_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2272_ = lean_usize_dec_eq(v_i_2269_, v_stop_2270_);
                if v___x_2272_ == 0 {
                    v___x_2273_ = 1usize;
                    v___x_2274_ = lean_usize_sub(v_i_2269_, v___x_2273_);
                    v___x_2275_ = lean_array_uget_borrowed(v_as_2268_, v___x_2274_);
                    v___x_2276_ = l_Std_DHashMap_Internal_AssocList_foldrM___at___00Std_Async_System_instReprEnvironment_repr_spec__1(v_b_2271_, v___x_2275_);
                    crate::leanh::lean_dec(v_b_2271_);
                    v_i_2269_ = v___x_2274_;
                    v_b_2271_ = v___x_2276_;
                    state = 0;
                    continue;
                } else {
                    return v_b_2271_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Std_Async_System_instReprEnvironment_repr_spec__2___boxed(
    mut v_as_2278_: *mut crate::leanh::LeanObject,
    mut v_i_2279_: *mut crate::leanh::LeanObject,
    mut v_stop_2280_: *mut crate::leanh::LeanObject,
    mut v_b_2281_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_i_boxed_2282_: usize = 0;
    let mut v_stop_boxed_2283_: usize = 0;
    let mut v_res_2284_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_i_boxed_2282_ = crate::leanh::lean_unbox_usize(v_i_2279_);
    crate::leanh::lean_dec(v_i_2279_);
    v_stop_boxed_2283_ = crate::leanh::lean_unbox_usize(v_stop_2280_);
    crate::leanh::lean_dec(v_stop_2280_);
    v_res_2284_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Std_Async_System_instReprEnvironment_repr_spec__2(v_as_2278_, v_i_boxed_2282_, v_stop_boxed_2283_, v_b_2281_);
    crate::leanh::lean_dec_ref(v_as_2278_);
    return v_res_2284_;
}
pub unsafe fn l_List_foldl___at___00Std_Format_joinSep___at___00Prod_repr___at___00List_repr___at___00Std_Async_System_instReprEnvironment_repr_spec__0_spec__0_spec__1_spec__4(
    mut v_x_2285_: *mut crate::leanh::LeanObject,
    mut v_x_2286_: *mut crate::leanh::LeanObject,
    mut v_x_2287_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_head_2288_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_2289_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2291_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2292_: u8 = 0;
    let mut v___x_2294_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2295_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2297_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2298_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_2287_) == 0 {
                    crate::leanh::lean_dec(v_x_2285_);
                    return v_x_2286_;
                } else {
                    v_head_2288_ = crate::leanh::lean_ctor_get(v_x_2287_, 0);
                    v_tail_2289_ = crate::leanh::lean_ctor_get(v_x_2287_, 1);
                    v_isSharedCheck_2298_ = (!crate::leanh::lean_is_exclusive(v_x_2287_)) as u8;
                    if v_isSharedCheck_2298_ == 0 {
                        v___x_2291_ = v_x_2287_;
                        v_isShared_2292_ = v_isSharedCheck_2298_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_tail_2289_);
                        crate::leanh::lean_inc(v_head_2288_);
                        crate::leanh::lean_dec(v_x_2287_);
                        v___x_2291_ = crate::leanh::lean_box(0);
                        v_isShared_2292_ = v_isSharedCheck_2298_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                crate::leanh::lean_inc(v_x_2285_);
                if v_isShared_2292_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_2291_, 5);
                    crate::leanh::lean_ctor_set(v___x_2291_, 1, v_x_2285_);
                    crate::leanh::lean_ctor_set(v___x_2291_, 0, v_x_2286_);
                    v___x_2294_ = v___x_2291_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2297_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2297_, 0, v_x_2286_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2297_, 1, v_x_2285_);
                    v___x_2294_ = v_reuseFailAlloc_2297_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_2295_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2295_, 0, v___x_2294_);
                crate::leanh::lean_ctor_set(v___x_2295_, 1, v_head_2288_);
                v_x_2286_ = v___x_2295_;
                v_x_2287_ = v_tail_2289_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Format_joinSep___at___00Prod_repr___at___00List_repr___at___00Std_Async_System_instReprEnvironment_repr_spec__0_spec__0_spec__1(
    mut v_x_2299_: *mut crate::leanh::LeanObject,
    mut v_x_2300_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_2299_) == 0 {
        let mut v___x_2301_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_x_2300_);
        v___x_2301_ = crate::leanh::lean_box(0);
        return v___x_2301_;
    } else {
        let mut v_tail_2302_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_tail_2302_ = crate::leanh::lean_ctor_get(v_x_2299_, 1);
        if crate::leanh::lean_obj_tag(v_tail_2302_) == 0 {
            let mut v_head_2303_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_x_2300_);
            v_head_2303_ = crate::leanh::lean_ctor_get(v_x_2299_, 0);
            crate::leanh::lean_inc(v_head_2303_);
            crate::leanh::lean_dec_ref_known(v_x_2299_, 2);
            return v_head_2303_;
        } else {
            let mut v_head_2304_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_2305_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_inc(v_tail_2302_);
            v_head_2304_ = crate::leanh::lean_ctor_get(v_x_2299_, 0);
            crate::leanh::lean_inc(v_head_2304_);
            crate::leanh::lean_dec_ref_known(v_x_2299_, 2);
            v___x_2305_ = l_List_foldl___at___00Std_Format_joinSep___at___00Prod_repr___at___00List_repr___at___00Std_Async_System_instReprEnvironment_repr_spec__0_spec__0_spec__1_spec__4(v_x_2300_, v_head_2304_, v_tail_2302_);
            return v___x_2305_;
        }
    }
}
pub unsafe fn _init_l_Prod_repr___at___00List_repr___at___00Std_Async_System_instReprEnvironment_repr_spec__0_spec__0___redArg___closed__2()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2308_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2309_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2308_ = l_Prod_repr___at___00List_repr___at___00Std_Async_System_instReprEnvironment_repr_spec__0_spec__0___redArg___closed__0;
    v___x_2309_ = lean_string_length(v___x_2308_);
    return v___x_2309_;
}
pub unsafe fn _init_l_Prod_repr___at___00List_repr___at___00Std_Async_System_instReprEnvironment_repr_spec__0_spec__0___redArg___closed__3()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2310_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2311_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2310_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Prod_repr___at___00List_repr___at___00Std_Async_System_instReprEnvironment_repr_spec__0_spec__0___redArg___closed__2), core::ptr::addr_of_mut!(l_Prod_repr___at___00List_repr___at___00Std_Async_System_instReprEnvironment_repr_spec__0_spec__0___redArg___closed__2_once), _init_l_Prod_repr___at___00List_repr___at___00Std_Async_System_instReprEnvironment_repr_spec__0_spec__0___redArg___closed__2);
    v___x_2311_ = lean_nat_to_int(v___x_2310_);
    return v___x_2311_;
}
pub unsafe fn l_Prod_repr___at___00List_repr___at___00Std_Async_System_instReprEnvironment_repr_spec__0_spec__0___redArg(
    mut v_x_2316_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_fst_2317_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2318_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2320_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2321_: u8 = 0;
    let mut v___x_2322_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2323_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2324_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2326_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2327_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2328_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2329_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2330_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2331_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2332_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2333_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2334_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2335_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2336_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2337_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2338_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2339_: u8 = 0;
    let mut v___x_2340_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2341_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2342_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_fst_2317_ = crate::leanh::lean_ctor_get(v_x_2316_, 0);
                v_snd_2318_ = crate::leanh::lean_ctor_get(v_x_2316_, 1);
                v_isSharedCheck_2342_ = (!crate::leanh::lean_is_exclusive(v_x_2316_)) as u8;
                if v_isSharedCheck_2342_ == 0 {
                    v___x_2320_ = v_x_2316_;
                    v_isShared_2321_ = v_isSharedCheck_2342_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_snd_2318_);
                    crate::leanh::lean_inc(v_fst_2317_);
                    crate::leanh::lean_dec(v_x_2316_);
                    v___x_2320_ = crate::leanh::lean_box(0);
                    v_isShared_2321_ = v_isSharedCheck_2342_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_2322_ = l_String_quote(v_fst_2317_);
                v___x_2323_ = crate::leanh::lean_alloc_ctor(3, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2323_, 0, v___x_2322_);
                v___x_2324_ = crate::leanh::lean_box(0);
                if v_isShared_2321_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_2320_, 1);
                    crate::leanh::lean_ctor_set(v___x_2320_, 1, v___x_2324_);
                    crate::leanh::lean_ctor_set(v___x_2320_, 0, v___x_2323_);
                    v___x_2326_ = v___x_2320_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2341_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2341_, 0, v___x_2323_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2341_, 1, v___x_2324_);
                    v___x_2326_ = v_reuseFailAlloc_2341_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_2327_ = l_String_quote(v_snd_2318_);
                v___x_2328_ = crate::leanh::lean_alloc_ctor(3, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2328_, 0, v___x_2327_);
                v___x_2329_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2329_, 0, v___x_2328_);
                crate::leanh::lean_ctor_set(v___x_2329_, 1, v___x_2326_);
                v___x_2330_ = l_List_reverse___redArg(v___x_2329_);
                v___x_2331_ = l_Array_repr___at___00Std_Async_System_instReprGroupInfo_repr_spec__0___closed__1;
                v___x_2332_ = l_Std_Format_joinSep___at___00Prod_repr___at___00List_repr___at___00Std_Async_System_instReprEnvironment_repr_spec__0_spec__0_spec__1(v___x_2330_, v___x_2331_);
                v___x_2333_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Prod_repr___at___00List_repr___at___00Std_Async_System_instReprEnvironment_repr_spec__0_spec__0___redArg___closed__3), core::ptr::addr_of_mut!(l_Prod_repr___at___00List_repr___at___00Std_Async_System_instReprEnvironment_repr_spec__0_spec__0___redArg___closed__3_once), _init_l_Prod_repr___at___00List_repr___at___00Std_Async_System_instReprEnvironment_repr_spec__0_spec__0___redArg___closed__3);
                v___x_2334_ = l_Prod_repr___at___00List_repr___at___00Std_Async_System_instReprEnvironment_repr_spec__0_spec__0___redArg___closed__4;
                v___x_2335_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2335_, 0, v___x_2334_);
                crate::leanh::lean_ctor_set(v___x_2335_, 1, v___x_2332_);
                v___x_2336_ = l_Prod_repr___at___00List_repr___at___00Std_Async_System_instReprEnvironment_repr_spec__0_spec__0___redArg___closed__5;
                v___x_2337_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2337_, 0, v___x_2335_);
                crate::leanh::lean_ctor_set(v___x_2337_, 1, v___x_2336_);
                v___x_2338_ = crate::leanh::lean_alloc_ctor(4, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2338_, 0, v___x_2333_);
                crate::leanh::lean_ctor_set(v___x_2338_, 1, v___x_2337_);
                v___x_2339_ = 0;
                v___x_2340_ = crate::leanh::lean_alloc_ctor(6, 1, (1) as u32);
                crate::leanh::lean_ctor_set(v___x_2340_, 0, v___x_2338_);
                crate::leanh::lean_ctor_set_uint8(
                    v___x_2340_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                    v___x_2339_,
                );
                return v___x_2340_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00List_repr___at___00Std_Async_System_instReprEnvironment_repr_spec__0_spec__1_spec__3_spec__7(
    mut v_x_2343_: *mut crate::leanh::LeanObject,
    mut v_x_2344_: *mut crate::leanh::LeanObject,
    mut v_x_2345_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_head_2346_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_2347_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2349_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2350_: u8 = 0;
    let mut v___x_2352_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2353_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2354_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2356_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2357_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_2345_) == 0 {
                    crate::leanh::lean_dec(v_x_2343_);
                    return v_x_2344_;
                } else {
                    v_head_2346_ = crate::leanh::lean_ctor_get(v_x_2345_, 0);
                    v_tail_2347_ = crate::leanh::lean_ctor_get(v_x_2345_, 1);
                    v_isSharedCheck_2357_ = (!crate::leanh::lean_is_exclusive(v_x_2345_)) as u8;
                    if v_isSharedCheck_2357_ == 0 {
                        v___x_2349_ = v_x_2345_;
                        v_isShared_2350_ = v_isSharedCheck_2357_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_tail_2347_);
                        crate::leanh::lean_inc(v_head_2346_);
                        crate::leanh::lean_dec(v_x_2345_);
                        v___x_2349_ = crate::leanh::lean_box(0);
                        v_isShared_2350_ = v_isSharedCheck_2357_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                crate::leanh::lean_inc(v_x_2343_);
                if v_isShared_2350_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_2349_, 5);
                    crate::leanh::lean_ctor_set(v___x_2349_, 1, v_x_2343_);
                    crate::leanh::lean_ctor_set(v___x_2349_, 0, v_x_2344_);
                    v___x_2352_ = v___x_2349_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2356_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2356_, 0, v_x_2344_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2356_, 1, v_x_2343_);
                    v___x_2352_ = v_reuseFailAlloc_2356_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_2353_ = l_Prod_repr___at___00List_repr___at___00Std_Async_System_instReprEnvironment_repr_spec__0_spec__0___redArg(v_head_2346_);
                v___x_2354_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2354_, 0, v___x_2352_);
                crate::leanh::lean_ctor_set(v___x_2354_, 1, v___x_2353_);
                v_x_2344_ = v___x_2354_;
                v_x_2345_ = v_tail_2347_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_List_foldl___at___00Std_Format_joinSep___at___00List_repr___at___00Std_Async_System_instReprEnvironment_repr_spec__0_spec__1_spec__3(
    mut v_x_2358_: *mut crate::leanh::LeanObject,
    mut v_x_2359_: *mut crate::leanh::LeanObject,
    mut v_x_2360_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_head_2361_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_2362_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2364_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2365_: u8 = 0;
    let mut v___x_2367_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2368_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2369_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2370_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2371_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2372_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_2360_) == 0 {
                    crate::leanh::lean_dec(v_x_2358_);
                    return v_x_2359_;
                } else {
                    v_head_2361_ = crate::leanh::lean_ctor_get(v_x_2360_, 0);
                    v_tail_2362_ = crate::leanh::lean_ctor_get(v_x_2360_, 1);
                    v_isSharedCheck_2372_ = (!crate::leanh::lean_is_exclusive(v_x_2360_)) as u8;
                    if v_isSharedCheck_2372_ == 0 {
                        v___x_2364_ = v_x_2360_;
                        v_isShared_2365_ = v_isSharedCheck_2372_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_tail_2362_);
                        crate::leanh::lean_inc(v_head_2361_);
                        crate::leanh::lean_dec(v_x_2360_);
                        v___x_2364_ = crate::leanh::lean_box(0);
                        v_isShared_2365_ = v_isSharedCheck_2372_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                crate::leanh::lean_inc(v_x_2358_);
                if v_isShared_2365_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_2364_, 5);
                    crate::leanh::lean_ctor_set(v___x_2364_, 1, v_x_2358_);
                    crate::leanh::lean_ctor_set(v___x_2364_, 0, v_x_2359_);
                    v___x_2367_ = v___x_2364_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2371_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2371_, 0, v_x_2359_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2371_, 1, v_x_2358_);
                    v___x_2367_ = v_reuseFailAlloc_2371_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_2368_ = l_Prod_repr___at___00List_repr___at___00Std_Async_System_instReprEnvironment_repr_spec__0_spec__0___redArg(v_head_2361_);
                v___x_2369_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2369_, 0, v___x_2367_);
                crate::leanh::lean_ctor_set(v___x_2369_, 1, v___x_2368_);
                v___x_2370_ = l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00List_repr___at___00Std_Async_System_instReprEnvironment_repr_spec__0_spec__1_spec__3_spec__7(v_x_2358_, v___x_2369_, v_tail_2362_);
                return v___x_2370_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Format_joinSep___at___00List_repr___at___00Std_Async_System_instReprEnvironment_repr_spec__0_spec__1(
    mut v_x_2373_: *mut crate::leanh::LeanObject,
    mut v_x_2374_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_2373_) == 0 {
        let mut v___x_2375_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_x_2374_);
        v___x_2375_ = crate::leanh::lean_box(0);
        return v___x_2375_;
    } else {
        let mut v_tail_2376_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_tail_2376_ = crate::leanh::lean_ctor_get(v_x_2373_, 1);
        if crate::leanh::lean_obj_tag(v_tail_2376_) == 0 {
            let mut v_head_2377_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_2378_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_x_2374_);
            v_head_2377_ = crate::leanh::lean_ctor_get(v_x_2373_, 0);
            crate::leanh::lean_inc(v_head_2377_);
            crate::leanh::lean_dec_ref_known(v_x_2373_, 2);
            v___x_2378_ = l_Prod_repr___at___00List_repr___at___00Std_Async_System_instReprEnvironment_repr_spec__0_spec__0___redArg(v_head_2377_);
            return v___x_2378_;
        } else {
            let mut v_head_2379_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_2380_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_2381_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_inc(v_tail_2376_);
            v_head_2379_ = crate::leanh::lean_ctor_get(v_x_2373_, 0);
            crate::leanh::lean_inc(v_head_2379_);
            crate::leanh::lean_dec_ref_known(v_x_2373_, 2);
            v___x_2380_ = l_Prod_repr___at___00List_repr___at___00Std_Async_System_instReprEnvironment_repr_spec__0_spec__0___redArg(v_head_2379_);
            v___x_2381_ = l_List_foldl___at___00Std_Format_joinSep___at___00List_repr___at___00Std_Async_System_instReprEnvironment_repr_spec__0_spec__1_spec__3(v_x_2374_, v___x_2380_, v_tail_2376_);
            return v___x_2381_;
        }
    }
}
pub unsafe fn _init_l_List_repr___at___00Std_Async_System_instReprEnvironment_repr_spec__0___redArg___closed__3()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2386_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2387_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2386_ =
        l_List_repr___at___00Std_Async_System_instReprEnvironment_repr_spec__0___redArg___closed__2;
    v___x_2387_ = lean_string_length(v___x_2386_);
    return v___x_2387_;
}
pub unsafe fn _init_l_List_repr___at___00Std_Async_System_instReprEnvironment_repr_spec__0___redArg___closed__4()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2388_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2389_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2388_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_List_repr___at___00Std_Async_System_instReprEnvironment_repr_spec__0___redArg___closed__3), core::ptr::addr_of_mut!(l_List_repr___at___00Std_Async_System_instReprEnvironment_repr_spec__0___redArg___closed__3_once), _init_l_List_repr___at___00Std_Async_System_instReprEnvironment_repr_spec__0___redArg___closed__3);
    v___x_2389_ = lean_nat_to_int(v___x_2388_);
    return v___x_2389_;
}
pub unsafe fn l_List_repr___at___00Std_Async_System_instReprEnvironment_repr_spec__0___redArg(
    mut v_a_2392_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_a_2392_) == 0 {
        let mut v___x_2393_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_2393_ = l_List_repr___at___00Std_Async_System_instReprEnvironment_repr_spec__0___redArg___closed__1;
        return v___x_2393_;
    } else {
        let mut v___x_2394_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2395_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2396_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2397_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2398_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2399_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2400_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2401_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2402_: u8 = 0;
        let mut v___x_2403_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_2394_ =
            l_Array_repr___at___00Std_Async_System_instReprGroupInfo_repr_spec__0___closed__1;
        v___x_2395_ = l_Std_Format_joinSep___at___00List_repr___at___00Std_Async_System_instReprEnvironment_repr_spec__0_spec__1(v_a_2392_, v___x_2394_);
        v___x_2396_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_List_repr___at___00Std_Async_System_instReprEnvironment_repr_spec__0___redArg___closed__4), core::ptr::addr_of_mut!(l_List_repr___at___00Std_Async_System_instReprEnvironment_repr_spec__0___redArg___closed__4_once), _init_l_List_repr___at___00Std_Async_System_instReprEnvironment_repr_spec__0___redArg___closed__4);
        v___x_2397_ = l_List_repr___at___00Std_Async_System_instReprEnvironment_repr_spec__0___redArg___closed__5;
        v___x_2398_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_2398_, 0, v___x_2397_);
        crate::leanh::lean_ctor_set(v___x_2398_, 1, v___x_2395_);
        v___x_2399_ =
            l_Array_repr___at___00Std_Async_System_instReprGroupInfo_repr_spec__0___closed__6;
        v___x_2400_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_2400_, 0, v___x_2398_);
        crate::leanh::lean_ctor_set(v___x_2400_, 1, v___x_2399_);
        v___x_2401_ = crate::leanh::lean_alloc_ctor(4, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_2401_, 0, v___x_2396_);
        crate::leanh::lean_ctor_set(v___x_2401_, 1, v___x_2400_);
        v___x_2402_ = 0;
        v___x_2403_ = crate::leanh::lean_alloc_ctor(6, 1, (1) as u32);
        crate::leanh::lean_ctor_set(v___x_2403_, 0, v___x_2401_);
        crate::leanh::lean_ctor_set_uint8(
            v___x_2403_,
            (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
            v___x_2402_,
        );
        return v___x_2403_;
    }
}
pub unsafe fn l_Std_Async_System_instReprEnvironment_repr___redArg(
    mut v_x_2416_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_buckets_2417_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2419_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2420_: u8 = 0;
    let mut v___x_2421_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2422_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2423_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2424_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2426_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2427_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2429_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2430_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2431_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2432_: u8 = 0;
    let mut v___x_2433_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2434_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2435_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2436_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2437_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2438_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2439_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2440_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2441_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2442_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2443_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2444_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2445_: u8 = 0;
    let mut v___x_2446_: usize = 0;
    let mut v___x_2447_: usize = 0;
    let mut v___x_2448_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2449_: u8 = 0;
    let mut v_unused_2450_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_buckets_2417_ = crate::leanh::lean_ctor_get(v_x_2416_, 1);
                v_isSharedCheck_2449_ = (!crate::leanh::lean_is_exclusive(v_x_2416_)) as u8;
                if v_isSharedCheck_2449_ == 0 {
                    v_unused_2450_ = crate::leanh::lean_ctor_get(v_x_2416_, 0);
                    crate::leanh::lean_dec(v_unused_2450_);
                    v___x_2419_ = v_x_2416_;
                    v_isShared_2420_ = v_isSharedCheck_2449_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_buckets_2417_);
                    crate::leanh::lean_dec(v_x_2416_);
                    v___x_2419_ = crate::leanh::lean_box(0);
                    v_isShared_2420_ = v_isSharedCheck_2449_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_2421_ = l_Std_Async_System_instReprEnvironment_repr___redArg___closed__3;
                v___x_2422_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Std_Async_System_instReprGroupInfo_repr___redArg___closed__4
                    ),
                    core::ptr::addr_of_mut!(
                        l_Std_Async_System_instReprGroupInfo_repr___redArg___closed__4_once
                    ),
                    _init_l_Std_Async_System_instReprGroupInfo_repr___redArg___closed__4,
                );
                v___x_2423_ = crate::leanh::lean_unsigned_to_nat(0);
                v___x_2424_ = l_Std_Async_System_instReprEnvironment_repr___redArg___closed__5;
                v___x_2443_ = crate::leanh::lean_box(0);
                v___x_2444_ = lean_array_get_size(v_buckets_2417_);
                v___x_2445_ = lean_nat_dec_lt(v___x_2423_, v___x_2444_);
                if v___x_2445_ == 0 {
                    crate::leanh::lean_dec_ref(v_buckets_2417_);
                    v___y_2426_ = v___x_2443_;
                    state = 2;
                    continue;
                } else {
                    v___x_2446_ = lean_usize_of_nat(v___x_2444_);
                    v___x_2447_ = 0usize;
                    v___x_2448_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Std_Async_System_instReprEnvironment_repr_spec__2(v_buckets_2417_, v___x_2446_, v___x_2447_, v___x_2443_);
                    crate::leanh::lean_dec_ref(v_buckets_2417_);
                    v___y_2426_ = v___x_2448_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_2427_ =
                    l_List_repr___at___00Std_Async_System_instReprEnvironment_repr_spec__0___redArg(
                        v___y_2426_,
                    );
                if v_isShared_2420_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_2419_, 5);
                    crate::leanh::lean_ctor_set(v___x_2419_, 1, v___x_2427_);
                    crate::leanh::lean_ctor_set(v___x_2419_, 0, v___x_2424_);
                    v___x_2429_ = v___x_2419_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_2442_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2442_, 0, v___x_2424_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2442_, 1, v___x_2427_);
                    v___x_2429_ = v_reuseFailAlloc_2442_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_2430_ = l_Repr_addAppParen(v___x_2429_, v___x_2423_);
                v___x_2431_ = crate::leanh::lean_alloc_ctor(4, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2431_, 0, v___x_2422_);
                crate::leanh::lean_ctor_set(v___x_2431_, 1, v___x_2430_);
                v___x_2432_ = 0;
                v___x_2433_ = crate::leanh::lean_alloc_ctor(6, 1, (1) as u32);
                crate::leanh::lean_ctor_set(v___x_2433_, 0, v___x_2431_);
                crate::leanh::lean_ctor_set_uint8(
                    v___x_2433_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                    v___x_2432_,
                );
                v___x_2434_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2434_, 0, v___x_2421_);
                crate::leanh::lean_ctor_set(v___x_2434_, 1, v___x_2433_);
                v___x_2435_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Std_Async_System_instReprSystemUser_repr___redArg___closed__23
                    ),
                    core::ptr::addr_of_mut!(
                        l_Std_Async_System_instReprSystemUser_repr___redArg___closed__23_once
                    ),
                    _init_l_Std_Async_System_instReprSystemUser_repr___redArg___closed__23,
                );
                v___x_2436_ = l_Std_Async_System_instReprSystemUser_repr___redArg___closed__24;
                v___x_2437_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2437_, 0, v___x_2436_);
                crate::leanh::lean_ctor_set(v___x_2437_, 1, v___x_2434_);
                v___x_2438_ = l_Std_Async_System_instReprSystemUser_repr___redArg___closed__25;
                v___x_2439_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2439_, 0, v___x_2437_);
                crate::leanh::lean_ctor_set(v___x_2439_, 1, v___x_2438_);
                v___x_2440_ = crate::leanh::lean_alloc_ctor(4, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2440_, 0, v___x_2435_);
                crate::leanh::lean_ctor_set(v___x_2440_, 1, v___x_2439_);
                v___x_2441_ = crate::leanh::lean_alloc_ctor(6, 1, (1) as u32);
                crate::leanh::lean_ctor_set(v___x_2441_, 0, v___x_2440_);
                crate::leanh::lean_ctor_set_uint8(
                    v___x_2441_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                    v___x_2432_,
                );
                return v___x_2441_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Async_System_instReprEnvironment_repr(
    mut v_x_2451_: *mut crate::leanh::LeanObject,
    mut v_prec_2452_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2453_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2453_ = l_Std_Async_System_instReprEnvironment_repr___redArg(v_x_2451_);
    return v___x_2453_;
}
pub unsafe fn l_Std_Async_System_instReprEnvironment_repr___boxed(
    mut v_x_2454_: *mut crate::leanh::LeanObject,
    mut v_prec_2455_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2456_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2456_ = l_Std_Async_System_instReprEnvironment_repr(v_x_2454_, v_prec_2455_);
    crate::leanh::lean_dec(v_prec_2455_);
    return v_res_2456_;
}
pub unsafe fn l_List_repr___at___00Std_Async_System_instReprEnvironment_repr_spec__0(
    mut v_a_2457_: *mut crate::leanh::LeanObject,
    mut v_n_2458_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2459_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2459_ =
        l_List_repr___at___00Std_Async_System_instReprEnvironment_repr_spec__0___redArg(v_a_2457_);
    return v___x_2459_;
}
pub unsafe fn l_List_repr___at___00Std_Async_System_instReprEnvironment_repr_spec__0___boxed(
    mut v_a_2460_: *mut crate::leanh::LeanObject,
    mut v_n_2461_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2462_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2462_ = l_List_repr___at___00Std_Async_System_instReprEnvironment_repr_spec__0(
        v_a_2460_, v_n_2461_,
    );
    crate::leanh::lean_dec(v_n_2461_);
    return v_res_2462_;
}
pub unsafe fn l_Prod_repr___at___00List_repr___at___00Std_Async_System_instReprEnvironment_repr_spec__0_spec__0(
    mut v_x_2463_: *mut crate::leanh::LeanObject,
    mut v_x_2464_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2465_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2465_ = l_Prod_repr___at___00List_repr___at___00Std_Async_System_instReprEnvironment_repr_spec__0_spec__0___redArg(v_x_2463_);
    return v___x_2465_;
}
pub unsafe fn l_Prod_repr___at___00List_repr___at___00Std_Async_System_instReprEnvironment_repr_spec__0_spec__0___boxed(
    mut v_x_2466_: *mut crate::leanh::LeanObject,
    mut v_x_2467_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2468_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2468_ = l_Prod_repr___at___00List_repr___at___00Std_Async_System_instReprEnvironment_repr_spec__0_spec__0(v_x_2466_, v_x_2467_);
    crate::leanh::lean_dec(v_x_2467_);
    return v_res_2468_;
}
pub unsafe fn _init_l_Std_Async_System_Environment_get_x3f___closed__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2472_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2473_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2472_ = crate::leanh::lean_alloc_closure(
        l_instDecidableEqString___boxed as *mut core::ffi::c_void,
        2,
        0,
    );
    v___f_2473_ = crate::leanh::lean_alloc_closure(
        l_instBEqOfDecidableEq___redArg___lam__0___boxed as *mut core::ffi::c_void,
        3,
        1,
    );
    crate::leanh::lean_closure_set(v___f_2473_, 0, v___x_2472_);
    return v___f_2473_;
}
pub unsafe fn l_Std_Async_System_Environment_get_x3f(
    mut v_env_2474_: *mut crate::leanh::LeanObject,
    mut v_key_2475_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2476_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2477_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2478_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2476_ = l_Std_Async_System_Environment_get_x3f___closed__0;
    v___f_2477_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Async_System_Environment_get_x3f___closed__1),
        core::ptr::addr_of_mut!(l_Std_Async_System_Environment_get_x3f___closed__1_once),
        _init_l_Std_Async_System_Environment_get_x3f___closed__1,
    );
    v___x_2478_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___redArg(
        v___f_2477_,
        v___x_2476_,
        v_env_2474_,
        v_key_2475_,
    );
    return v___x_2478_;
}
pub unsafe fn l_Std_Async_System_Environment_get_x3f___boxed(
    mut v_env_2479_: *mut crate::leanh::LeanObject,
    mut v_key_2480_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2481_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2481_ = l_Std_Async_System_Environment_get_x3f(v_env_2479_, v_key_2480_);
    crate::leanh::lean_dec_ref(v_env_2479_);
    return v_res_2481_;
}
pub unsafe fn l_Std_Async_System_getSystemInfo() -> *mut crate::leanh::LeanObject {
    let mut v___x_2483_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2484_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2486_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2487_: u8 = 0;
    let mut v_sysname_2488_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_release_2489_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_version_2490_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_machine_2491_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2493_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2494_: u8 = 0;
    let mut v___x_2496_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2498_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2499_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2500_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2501_: u8 = 0;
    let mut v_isSharedCheck_2502_: u8 = 0;
    let mut v_a_2503_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2505_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2506_: u8 = 0;
    let mut v___x_2508_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2509_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2510_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2483_ = lean_uv_os_uname();
                if crate::leanh::lean_obj_tag(v___x_2483_) == 0 {
                    v_a_2484_ = crate::leanh::lean_ctor_get(v___x_2483_, 0);
                    v_isSharedCheck_2502_ = (!crate::leanh::lean_is_exclusive(v___x_2483_)) as u8;
                    if v_isSharedCheck_2502_ == 0 {
                        v___x_2486_ = v___x_2483_;
                        v_isShared_2487_ = v_isSharedCheck_2502_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_2484_);
                        crate::leanh::lean_dec(v___x_2483_);
                        v___x_2486_ = crate::leanh::lean_box(0);
                        v_isShared_2487_ = v_isSharedCheck_2502_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_2503_ = crate::leanh::lean_ctor_get(v___x_2483_, 0);
                    v_isSharedCheck_2510_ = (!crate::leanh::lean_is_exclusive(v___x_2483_)) as u8;
                    if v_isSharedCheck_2510_ == 0 {
                        v___x_2505_ = v___x_2483_;
                        v_isShared_2506_ = v_isSharedCheck_2510_;
                        state = 5;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_2503_);
                        crate::leanh::lean_dec(v___x_2483_);
                        v___x_2505_ = crate::leanh::lean_box(0);
                        v_isShared_2506_ = v_isSharedCheck_2510_;
                        state = 5;
                        continue;
                    }
                }
            }
            1 => {
                v_sysname_2488_ = crate::leanh::lean_ctor_get(v_a_2484_, 0);
                v_release_2489_ = crate::leanh::lean_ctor_get(v_a_2484_, 1);
                v_version_2490_ = crate::leanh::lean_ctor_get(v_a_2484_, 2);
                v_machine_2491_ = crate::leanh::lean_ctor_get(v_a_2484_, 3);
                v_isSharedCheck_2501_ = (!crate::leanh::lean_is_exclusive(v_a_2484_)) as u8;
                if v_isSharedCheck_2501_ == 0 {
                    v___x_2493_ = v_a_2484_;
                    v_isShared_2494_ = v_isSharedCheck_2501_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_machine_2491_);
                    crate::leanh::lean_inc(v_version_2490_);
                    crate::leanh::lean_inc(v_release_2489_);
                    crate::leanh::lean_inc(v_sysname_2488_);
                    crate::leanh::lean_dec(v_a_2484_);
                    v___x_2493_ = crate::leanh::lean_box(0);
                    v_isShared_2494_ = v_isSharedCheck_2501_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                if v_isShared_2494_ == 0 {
                    v___x_2496_ = v___x_2493_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_2500_ = crate::leanh::lean_alloc_ctor(0, 4, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2500_, 0, v_sysname_2488_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2500_, 1, v_release_2489_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2500_, 2, v_version_2490_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2500_, 3, v_machine_2491_);
                    v___x_2496_ = v_reuseFailAlloc_2500_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_2487_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2486_, 0, v___x_2496_);
                    v___x_2498_ = v___x_2486_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2499_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2499_, 0, v___x_2496_);
                    v___x_2498_ = v_reuseFailAlloc_2499_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_2498_;
            }
            5 => {
                if v_isShared_2506_ == 0 {
                    v___x_2508_ = v___x_2505_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_2509_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2509_, 0, v_a_2503_);
                    v___x_2508_ = v_reuseFailAlloc_2509_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_2508_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Async_System_getSystemInfo___boxed(
    mut v_a_2511_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2512_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2512_ = l_Std_Async_System_getSystemInfo();
    return v_res_2512_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_Async_System_getCPUInfo_spec__1_spec__1(
    mut v_sz_2513_: usize,
    mut v_i_2514_: usize,
    mut v_bs_2515_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2516_: u8 = 0;
    let mut v_v_2517_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_times_2518_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_model_2519_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_speed_2520_: u64 = 0;
    let mut v_user_2521_: u64 = 0;
    let mut v_nice_2522_: u64 = 0;
    let mut v_sys_2523_: u64 = 0;
    let mut v_idle_2524_: u64 = 0;
    let mut v_irq_2525_: u64 = 0;
    let mut v___x_2526_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_bs_x27_2527_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2528_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2529_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2530_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2531_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2532_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2533_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2534_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2535_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2536_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2537_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2538_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2539_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2540_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2541_: usize = 0;
    let mut v___x_2542_: usize = 0;
    let mut v___x_2543_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2516_ = lean_usize_dec_lt(v_i_2514_, v_sz_2513_);
                if v___x_2516_ == 0 {
                    return v_bs_2515_;
                } else {
                    v_v_2517_ = lean_array_uget_borrowed(v_bs_2515_, v_i_2514_);
                    v_times_2518_ = crate::leanh::lean_ctor_get(v_v_2517_, 1);
                    v_model_2519_ = crate::leanh::lean_ctor_get(v_v_2517_, 0);
                    crate::leanh::lean_inc_ref(v_model_2519_);
                    v_speed_2520_ = crate::leanh::lean_ctor_get_uint64(
                        v_v_2517_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2) as u32,
                    );
                    v_user_2521_ = crate::leanh::lean_ctor_get_uint64(v_times_2518_, 0 as u32);
                    v_nice_2522_ = crate::leanh::lean_ctor_get_uint64(v_times_2518_, 8 as u32);
                    v_sys_2523_ = crate::leanh::lean_ctor_get_uint64(v_times_2518_, 16 as u32);
                    v_idle_2524_ = crate::leanh::lean_ctor_get_uint64(v_times_2518_, 24 as u32);
                    v_irq_2525_ = crate::leanh::lean_ctor_get_uint64(v_times_2518_, 32 as u32);
                    v___x_2526_ = crate::leanh::lean_unsigned_to_nat(0);
                    v_bs_x27_2527_ = lean_array_uset(v_bs_2515_, v_i_2514_, v___x_2526_);
                    v___x_2528_ = lean_uint64_to_nat(v_speed_2520_);
                    v___x_2529_ = lean_uint64_to_nat(v_user_2521_);
                    v___x_2530_ = lean_nat_to_int(v___x_2529_);
                    v___x_2531_ = lean_uint64_to_nat(v_nice_2522_);
                    v___x_2532_ = lean_nat_to_int(v___x_2531_);
                    v___x_2533_ = lean_uint64_to_nat(v_sys_2523_);
                    v___x_2534_ = lean_nat_to_int(v___x_2533_);
                    v___x_2535_ = lean_uint64_to_nat(v_idle_2524_);
                    v___x_2536_ = lean_nat_to_int(v___x_2535_);
                    v___x_2537_ = lean_uint64_to_nat(v_irq_2525_);
                    v___x_2538_ = lean_nat_to_int(v___x_2537_);
                    v___x_2539_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_2539_, 0, v___x_2530_);
                    crate::leanh::lean_ctor_set(v___x_2539_, 1, v___x_2532_);
                    crate::leanh::lean_ctor_set(v___x_2539_, 2, v___x_2534_);
                    crate::leanh::lean_ctor_set(v___x_2539_, 3, v___x_2536_);
                    crate::leanh::lean_ctor_set(v___x_2539_, 4, v___x_2538_);
                    v___x_2540_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_2540_, 0, v_model_2519_);
                    crate::leanh::lean_ctor_set(v___x_2540_, 1, v___x_2528_);
                    crate::leanh::lean_ctor_set(v___x_2540_, 2, v___x_2539_);
                    v___x_2541_ = 1usize;
                    v___x_2542_ = lean_usize_add(v_i_2514_, v___x_2541_);
                    v___x_2543_ = lean_array_uset(v_bs_x27_2527_, v_i_2514_, v___x_2540_);
                    v_i_2514_ = v___x_2542_;
                    v_bs_2515_ = v___x_2543_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_Async_System_getCPUInfo_spec__1_spec__1___boxed(
    mut v_sz_2545_: *mut crate::leanh::LeanObject,
    mut v_i_2546_: *mut crate::leanh::LeanObject,
    mut v_bs_2547_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_sz_boxed_2548_: usize = 0;
    let mut v_i_boxed_2549_: usize = 0;
    let mut v_res_2550_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_2548_ = crate::leanh::lean_unbox_usize(v_sz_2545_);
    crate::leanh::lean_dec(v_sz_2545_);
    v_i_boxed_2549_ = crate::leanh::lean_unbox_usize(v_i_2546_);
    crate::leanh::lean_dec(v_i_2546_);
    v_res_2550_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_Async_System_getCPUInfo_spec__1_spec__1(v_sz_boxed_2548_, v_i_boxed_2549_, v_bs_2547_);
    return v_res_2550_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_Async_System_getCPUInfo_spec__1(
    mut v_sz_2551_: usize,
    mut v_i_2552_: usize,
    mut v_bs_2553_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2554_: u8 = 0;
    v___x_2554_ = lean_usize_dec_lt(v_i_2552_, v_sz_2551_);
    if v___x_2554_ == 0 {
        return v_bs_2553_;
    } else {
        let mut v_v_2555_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_times_2556_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_model_2557_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_speed_2558_: u64 = 0;
        let mut v_user_2559_: u64 = 0;
        let mut v_nice_2560_: u64 = 0;
        let mut v_sys_2561_: u64 = 0;
        let mut v_idle_2562_: u64 = 0;
        let mut v_irq_2563_: u64 = 0;
        let mut v___x_2564_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_bs_x27_2565_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2566_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2567_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2568_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2569_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2570_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2571_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2572_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2573_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2574_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2575_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2576_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2577_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2578_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2579_: usize = 0;
        let mut v___x_2580_: usize = 0;
        let mut v___x_2581_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2582_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_v_2555_ = lean_array_uget_borrowed(v_bs_2553_, v_i_2552_);
        v_times_2556_ = crate::leanh::lean_ctor_get(v_v_2555_, 1);
        v_model_2557_ = crate::leanh::lean_ctor_get(v_v_2555_, 0);
        crate::leanh::lean_inc_ref(v_model_2557_);
        v_speed_2558_ = crate::leanh::lean_ctor_get_uint64(
            v_v_2555_,
            (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2) as u32,
        );
        v_user_2559_ = crate::leanh::lean_ctor_get_uint64(v_times_2556_, 0 as u32);
        v_nice_2560_ = crate::leanh::lean_ctor_get_uint64(v_times_2556_, 8 as u32);
        v_sys_2561_ = crate::leanh::lean_ctor_get_uint64(v_times_2556_, 16 as u32);
        v_idle_2562_ = crate::leanh::lean_ctor_get_uint64(v_times_2556_, 24 as u32);
        v_irq_2563_ = crate::leanh::lean_ctor_get_uint64(v_times_2556_, 32 as u32);
        v___x_2564_ = crate::leanh::lean_unsigned_to_nat(0);
        v_bs_x27_2565_ = lean_array_uset(v_bs_2553_, v_i_2552_, v___x_2564_);
        v___x_2566_ = lean_uint64_to_nat(v_speed_2558_);
        v___x_2567_ = lean_uint64_to_nat(v_user_2559_);
        v___x_2568_ = lean_nat_to_int(v___x_2567_);
        v___x_2569_ = lean_uint64_to_nat(v_nice_2560_);
        v___x_2570_ = lean_nat_to_int(v___x_2569_);
        v___x_2571_ = lean_uint64_to_nat(v_sys_2561_);
        v___x_2572_ = lean_nat_to_int(v___x_2571_);
        v___x_2573_ = lean_uint64_to_nat(v_idle_2562_);
        v___x_2574_ = lean_nat_to_int(v___x_2573_);
        v___x_2575_ = lean_uint64_to_nat(v_irq_2563_);
        v___x_2576_ = lean_nat_to_int(v___x_2575_);
        v___x_2577_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_2577_, 0, v___x_2568_);
        crate::leanh::lean_ctor_set(v___x_2577_, 1, v___x_2570_);
        crate::leanh::lean_ctor_set(v___x_2577_, 2, v___x_2572_);
        crate::leanh::lean_ctor_set(v___x_2577_, 3, v___x_2574_);
        crate::leanh::lean_ctor_set(v___x_2577_, 4, v___x_2576_);
        v___x_2578_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_2578_, 0, v_model_2557_);
        crate::leanh::lean_ctor_set(v___x_2578_, 1, v___x_2566_);
        crate::leanh::lean_ctor_set(v___x_2578_, 2, v___x_2577_);
        v___x_2579_ = 1usize;
        v___x_2580_ = lean_usize_add(v_i_2552_, v___x_2579_);
        v___x_2581_ = lean_array_uset(v_bs_x27_2565_, v_i_2552_, v___x_2578_);
        v___x_2582_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_Async_System_getCPUInfo_spec__1_spec__1(v_sz_2551_, v___x_2580_, v___x_2581_);
        return v___x_2582_;
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_Async_System_getCPUInfo_spec__1___boxed(
    mut v_sz_2583_: *mut crate::leanh::LeanObject,
    mut v_i_2584_: *mut crate::leanh::LeanObject,
    mut v_bs_2585_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_sz_boxed_2586_: usize = 0;
    let mut v_i_boxed_2587_: usize = 0;
    let mut v_res_2588_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_2586_ = crate::leanh::lean_unbox_usize(v_sz_2583_);
    crate::leanh::lean_dec(v_sz_2583_);
    v_i_boxed_2587_ = crate::leanh::lean_unbox_usize(v_i_2584_);
    crate::leanh::lean_dec(v_i_2584_);
    v_res_2588_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_Async_System_getCPUInfo_spec__1(v_sz_boxed_2586_, v_i_boxed_2587_, v_bs_2585_);
    return v_res_2588_;
}
pub unsafe fn l_Std_Async_System_getCPUInfo() -> *mut crate::leanh::LeanObject {
    let mut v___x_2590_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2591_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2593_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2594_: u8 = 0;
    let mut v_sz_2595_: usize = 0;
    let mut v___x_2596_: usize = 0;
    let mut v___x_2597_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2599_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2600_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2601_: u8 = 0;
    let mut v_a_2602_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2604_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2605_: u8 = 0;
    let mut v___x_2607_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2608_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2609_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2590_ = lean_uv_cpu_info();
                if crate::leanh::lean_obj_tag(v___x_2590_) == 0 {
                    v_a_2591_ = crate::leanh::lean_ctor_get(v___x_2590_, 0);
                    v_isSharedCheck_2601_ = (!crate::leanh::lean_is_exclusive(v___x_2590_)) as u8;
                    if v_isSharedCheck_2601_ == 0 {
                        v___x_2593_ = v___x_2590_;
                        v_isShared_2594_ = v_isSharedCheck_2601_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_2591_);
                        crate::leanh::lean_dec(v___x_2590_);
                        v___x_2593_ = crate::leanh::lean_box(0);
                        v_isShared_2594_ = v_isSharedCheck_2601_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_2602_ = crate::leanh::lean_ctor_get(v___x_2590_, 0);
                    v_isSharedCheck_2609_ = (!crate::leanh::lean_is_exclusive(v___x_2590_)) as u8;
                    if v_isSharedCheck_2609_ == 0 {
                        v___x_2604_ = v___x_2590_;
                        v_isShared_2605_ = v_isSharedCheck_2609_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_2602_);
                        crate::leanh::lean_dec(v___x_2590_);
                        v___x_2604_ = crate::leanh::lean_box(0);
                        v_isShared_2605_ = v_isSharedCheck_2609_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v_sz_2595_ = lean_array_size(v_a_2591_);
                v___x_2596_ = 0usize;
                v___x_2597_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_Async_System_getCPUInfo_spec__1(v_sz_2595_, v___x_2596_, v_a_2591_);
                if v_isShared_2594_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2593_, 0, v___x_2597_);
                    v___x_2599_ = v___x_2593_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2600_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2600_, 0, v___x_2597_);
                    v___x_2599_ = v_reuseFailAlloc_2600_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_2599_;
            }
            3 => {
                if v_isShared_2605_ == 0 {
                    v___x_2607_ = v___x_2604_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2608_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2608_, 0, v_a_2602_);
                    v___x_2607_ = v_reuseFailAlloc_2608_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_2607_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Async_System_getCPUInfo___boxed(
    mut v_a_2610_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2611_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2611_ = l_Std_Async_System_getCPUInfo();
    return v_res_2611_;
}
pub unsafe fn l_Nat_cast___at___00Std_Async_System_getCPUInfo_spec__0(
    mut v_a_2612_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2613_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2614_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2613_ = lean_nat_to_int(v_a_2612_);
    v___x_2614_ = l_Rat_ofInt(v___x_2613_);
    return v___x_2614_;
}
pub unsafe fn l_Std_Async_System_getUpTime() -> *mut crate::leanh::LeanObject {
    let mut v___x_2616_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2617_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2619_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2620_: u8 = 0;
    let mut v___x_2621_: u64 = 0;
    let mut v___x_2622_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2623_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2625_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2626_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2627_: u8 = 0;
    let mut v_a_2628_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2630_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2631_: u8 = 0;
    let mut v___x_2633_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2634_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2635_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2616_ = lean_uv_uptime();
                if crate::leanh::lean_obj_tag(v___x_2616_) == 0 {
                    v_a_2617_ = crate::leanh::lean_ctor_get(v___x_2616_, 0);
                    v_isSharedCheck_2627_ = (!crate::leanh::lean_is_exclusive(v___x_2616_)) as u8;
                    if v_isSharedCheck_2627_ == 0 {
                        v___x_2619_ = v___x_2616_;
                        v_isShared_2620_ = v_isSharedCheck_2627_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_2617_);
                        crate::leanh::lean_dec(v___x_2616_);
                        v___x_2619_ = crate::leanh::lean_box(0);
                        v_isShared_2620_ = v_isSharedCheck_2627_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_2628_ = crate::leanh::lean_ctor_get(v___x_2616_, 0);
                    v_isSharedCheck_2635_ = (!crate::leanh::lean_is_exclusive(v___x_2616_)) as u8;
                    if v_isSharedCheck_2635_ == 0 {
                        v___x_2630_ = v___x_2616_;
                        v_isShared_2631_ = v_isSharedCheck_2635_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_2628_);
                        crate::leanh::lean_dec(v___x_2616_);
                        v___x_2630_ = crate::leanh::lean_box(0);
                        v_isShared_2631_ = v_isSharedCheck_2635_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v___x_2621_ = crate::leanh::lean_unbox_uint64(v_a_2617_);
                crate::leanh::lean_dec(v_a_2617_);
                v___x_2622_ = lean_uint64_to_nat(v___x_2621_);
                v___x_2623_ = lean_nat_to_int(v___x_2622_);
                if v_isShared_2620_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2619_, 0, v___x_2623_);
                    v___x_2625_ = v___x_2619_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2626_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2626_, 0, v___x_2623_);
                    v___x_2625_ = v_reuseFailAlloc_2626_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_2625_;
            }
            3 => {
                if v_isShared_2631_ == 0 {
                    v___x_2633_ = v___x_2630_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2634_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2634_, 0, v_a_2628_);
                    v___x_2633_ = v_reuseFailAlloc_2634_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_2633_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Async_System_getUpTime___boxed(
    mut v_a_2636_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2637_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2637_ = l_Std_Async_System_getUpTime();
    return v_res_2637_;
}
pub unsafe fn l_Std_Async_System_getHighResolutionTime() -> *mut crate::leanh::LeanObject {
    let mut v___x_2639_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2640_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2642_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2643_: u8 = 0;
    let mut v___x_2644_: u64 = 0;
    let mut v___x_2645_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2646_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2648_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2649_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2650_: u8 = 0;
    let mut v_a_2651_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2653_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2654_: u8 = 0;
    let mut v___x_2656_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2657_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2658_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2639_ = lean_uv_hrtime();
                if crate::leanh::lean_obj_tag(v___x_2639_) == 0 {
                    v_a_2640_ = crate::leanh::lean_ctor_get(v___x_2639_, 0);
                    v_isSharedCheck_2650_ = (!crate::leanh::lean_is_exclusive(v___x_2639_)) as u8;
                    if v_isSharedCheck_2650_ == 0 {
                        v___x_2642_ = v___x_2639_;
                        v_isShared_2643_ = v_isSharedCheck_2650_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_2640_);
                        crate::leanh::lean_dec(v___x_2639_);
                        v___x_2642_ = crate::leanh::lean_box(0);
                        v_isShared_2643_ = v_isSharedCheck_2650_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_2651_ = crate::leanh::lean_ctor_get(v___x_2639_, 0);
                    v_isSharedCheck_2658_ = (!crate::leanh::lean_is_exclusive(v___x_2639_)) as u8;
                    if v_isSharedCheck_2658_ == 0 {
                        v___x_2653_ = v___x_2639_;
                        v_isShared_2654_ = v_isSharedCheck_2658_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_2651_);
                        crate::leanh::lean_dec(v___x_2639_);
                        v___x_2653_ = crate::leanh::lean_box(0);
                        v_isShared_2654_ = v_isSharedCheck_2658_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v___x_2644_ = crate::leanh::lean_unbox_uint64(v_a_2640_);
                crate::leanh::lean_dec(v_a_2640_);
                v___x_2645_ = lean_uint64_to_nat(v___x_2644_);
                v___x_2646_ = lean_nat_to_int(v___x_2645_);
                if v_isShared_2643_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2642_, 0, v___x_2646_);
                    v___x_2648_ = v___x_2642_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2649_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2649_, 0, v___x_2646_);
                    v___x_2648_ = v_reuseFailAlloc_2649_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_2648_;
            }
            3 => {
                if v_isShared_2654_ == 0 {
                    v___x_2656_ = v___x_2653_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2657_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2657_, 0, v_a_2651_);
                    v___x_2656_ = v_reuseFailAlloc_2657_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_2656_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Async_System_getHighResolutionTime___boxed(
    mut v_a_2659_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2660_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2660_ = l_Std_Async_System_getHighResolutionTime();
    return v_res_2660_;
}
pub unsafe fn l_Std_Async_System_getHostName() -> *mut crate::leanh::LeanObject {
    let mut v___x_2662_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2662_ = lean_uv_os_gethostname();
    return v___x_2662_;
}
pub unsafe fn l_Std_Async_System_getHostName___boxed(
    mut v_a_2663_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2664_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2664_ = l_Std_Async_System_getHostName();
    return v_res_2664_;
}
pub unsafe fn l_Std_Async_System_setEnvVar(
    mut v_name_2665_: *mut crate::leanh::LeanObject,
    mut v_value_2666_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2668_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2668_ = lean_uv_os_setenv(v_name_2665_, v_value_2666_);
    return v___x_2668_;
}
pub unsafe fn l_Std_Async_System_setEnvVar___boxed(
    mut v_name_2669_: *mut crate::leanh::LeanObject,
    mut v_value_2670_: *mut crate::leanh::LeanObject,
    mut v_a_2671_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2672_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2672_ = l_Std_Async_System_setEnvVar(v_name_2669_, v_value_2670_);
    crate::leanh::lean_dec_ref(v_value_2670_);
    crate::leanh::lean_dec_ref(v_name_2669_);
    return v_res_2672_;
}
pub unsafe fn l_Std_Async_System_getEnvVar(
    mut v_name_2673_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2675_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2675_ = lean_uv_os_getenv(v_name_2673_);
    return v___x_2675_;
}
pub unsafe fn l_Std_Async_System_getEnvVar___boxed(
    mut v_name_2676_: *mut crate::leanh::LeanObject,
    mut v_a_2677_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2678_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2678_ = l_Std_Async_System_getEnvVar(v_name_2676_);
    crate::leanh::lean_dec_ref(v_name_2676_);
    return v_res_2678_;
}
pub unsafe fn l_Std_Async_System_unsetEnvVar(
    mut v_name_2679_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2681_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2681_ = lean_uv_os_unsetenv(v_name_2679_);
    return v___x_2681_;
}
pub unsafe fn l_Std_Async_System_unsetEnvVar___boxed(
    mut v_name_2682_: *mut crate::leanh::LeanObject,
    mut v_a_2683_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2684_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2684_ = l_Std_Async_System_unsetEnvVar(v_name_2682_);
    crate::leanh::lean_dec_ref(v_name_2682_);
    return v_res_2684_;
}
pub unsafe fn l_Std_Async_System_getEnv() -> *mut crate::leanh::LeanObject {
    let mut v___x_2709_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2710_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2712_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2713_: u8 = 0;
    let mut v___x_2714_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2715_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2716_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2717_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2718_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2719_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2720_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2721_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2722_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2723_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2724_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2725_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2726_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2727_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2729_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2730_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2731_: u8 = 0;
    let mut v_a_2732_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2734_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2735_: u8 = 0;
    let mut v___x_2737_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2738_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2739_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2709_ = lean_uv_os_environ();
                if crate::leanh::lean_obj_tag(v___x_2709_) == 0 {
                    v_a_2710_ = crate::leanh::lean_ctor_get(v___x_2709_, 0);
                    v_isSharedCheck_2731_ = (!crate::leanh::lean_is_exclusive(v___x_2709_)) as u8;
                    if v_isSharedCheck_2731_ == 0 {
                        v___x_2712_ = v___x_2709_;
                        v_isShared_2713_ = v_isSharedCheck_2731_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_2710_);
                        crate::leanh::lean_dec(v___x_2709_);
                        v___x_2712_ = crate::leanh::lean_box(0);
                        v_isShared_2713_ = v_isSharedCheck_2731_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_2732_ = crate::leanh::lean_ctor_get(v___x_2709_, 0);
                    v_isSharedCheck_2739_ = (!crate::leanh::lean_is_exclusive(v___x_2709_)) as u8;
                    if v_isSharedCheck_2739_ == 0 {
                        v___x_2734_ = v___x_2709_;
                        v_isShared_2735_ = v_isSharedCheck_2739_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_2732_);
                        crate::leanh::lean_dec(v___x_2709_);
                        v___x_2734_ = crate::leanh::lean_box(0);
                        v_isShared_2735_ = v_isSharedCheck_2739_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v___x_2714_ = l_Std_Async_System_Environment_get_x3f___closed__0;
                v___f_2715_ = l_Std_Async_System_getEnv___closed__11;
                v___f_2716_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Std_Async_System_Environment_get_x3f___closed__1),
                    core::ptr::addr_of_mut!(
                        l_Std_Async_System_Environment_get_x3f___closed__1_once
                    ),
                    _init_l_Std_Async_System_Environment_get_x3f___closed__1,
                );
                v___x_2717_ = lean_array_get_size(v_a_2710_);
                v___x_2718_ = crate::leanh::lean_unsigned_to_nat(0);
                v___x_2719_ = crate::leanh::lean_unsigned_to_nat(4);
                v___x_2720_ = lean_nat_mul(v___x_2717_, v___x_2719_);
                v___x_2721_ = crate::leanh::lean_unsigned_to_nat(3);
                v___x_2722_ = lean_nat_div(v___x_2720_, v___x_2721_);
                crate::leanh::lean_dec(v___x_2720_);
                v___x_2723_ = l_Nat_nextPowerOfTwo(v___x_2722_);
                crate::leanh::lean_dec(v___x_2722_);
                v___x_2724_ = crate::leanh::lean_box(0);
                v___x_2725_ = lean_mk_array(v___x_2723_, v___x_2724_);
                v___x_2726_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2726_, 0, v___x_2718_);
                crate::leanh::lean_ctor_set(v___x_2726_, 1, v___x_2725_);
                v___x_2727_ = l_Std_DHashMap_Internal_Raw_u2080_Const_insertMany___redArg(
                    v___f_2715_,
                    v___f_2716_,
                    v___x_2714_,
                    v___x_2726_,
                    v_a_2710_,
                );
                if v_isShared_2713_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2712_, 0, v___x_2727_);
                    v___x_2729_ = v___x_2712_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2730_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2730_, 0, v___x_2727_);
                    v___x_2729_ = v_reuseFailAlloc_2730_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_2729_;
            }
            3 => {
                if v_isShared_2735_ == 0 {
                    v___x_2737_ = v___x_2734_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2738_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2738_, 0, v_a_2732_);
                    v___x_2737_ = v_reuseFailAlloc_2738_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_2737_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Async_System_getEnv___boxed(
    mut v_a_2740_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2741_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2741_ = l_Std_Async_System_getEnv();
    return v_res_2741_;
}
pub unsafe fn l_Std_Async_System_getHomeDir() -> *mut crate::leanh::LeanObject {
    let mut v___x_2743_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2744_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2746_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2747_: u8 = 0;
    let mut v___x_2749_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2750_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2751_: u8 = 0;
    let mut v_a_2752_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2754_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2755_: u8 = 0;
    let mut v___x_2757_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2758_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2759_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2743_ = lean_uv_os_homedir();
                if crate::leanh::lean_obj_tag(v___x_2743_) == 0 {
                    v_a_2744_ = crate::leanh::lean_ctor_get(v___x_2743_, 0);
                    v_isSharedCheck_2751_ = (!crate::leanh::lean_is_exclusive(v___x_2743_)) as u8;
                    if v_isSharedCheck_2751_ == 0 {
                        v___x_2746_ = v___x_2743_;
                        v_isShared_2747_ = v_isSharedCheck_2751_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_2744_);
                        crate::leanh::lean_dec(v___x_2743_);
                        v___x_2746_ = crate::leanh::lean_box(0);
                        v_isShared_2747_ = v_isSharedCheck_2751_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_2752_ = crate::leanh::lean_ctor_get(v___x_2743_, 0);
                    v_isSharedCheck_2759_ = (!crate::leanh::lean_is_exclusive(v___x_2743_)) as u8;
                    if v_isSharedCheck_2759_ == 0 {
                        v___x_2754_ = v___x_2743_;
                        v_isShared_2755_ = v_isSharedCheck_2759_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_2752_);
                        crate::leanh::lean_dec(v___x_2743_);
                        v___x_2754_ = crate::leanh::lean_box(0);
                        v_isShared_2755_ = v_isSharedCheck_2759_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_2747_ == 0 {
                    v___x_2749_ = v___x_2746_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2750_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2750_, 0, v_a_2744_);
                    v___x_2749_ = v_reuseFailAlloc_2750_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_2749_;
            }
            3 => {
                if v_isShared_2755_ == 0 {
                    v___x_2757_ = v___x_2754_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2758_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2758_, 0, v_a_2752_);
                    v___x_2757_ = v_reuseFailAlloc_2758_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_2757_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Async_System_getHomeDir___boxed(
    mut v_a_2760_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2761_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2761_ = l_Std_Async_System_getHomeDir();
    return v_res_2761_;
}
pub unsafe fn l_Std_Async_System_getTmpDir() -> *mut crate::leanh::LeanObject {
    let mut v___x_2763_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2764_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2766_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2767_: u8 = 0;
    let mut v___x_2769_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2770_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2771_: u8 = 0;
    let mut v_a_2772_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2774_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2775_: u8 = 0;
    let mut v___x_2777_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2778_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2779_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2763_ = lean_uv_os_tmpdir();
                if crate::leanh::lean_obj_tag(v___x_2763_) == 0 {
                    v_a_2764_ = crate::leanh::lean_ctor_get(v___x_2763_, 0);
                    v_isSharedCheck_2771_ = (!crate::leanh::lean_is_exclusive(v___x_2763_)) as u8;
                    if v_isSharedCheck_2771_ == 0 {
                        v___x_2766_ = v___x_2763_;
                        v_isShared_2767_ = v_isSharedCheck_2771_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_2764_);
                        crate::leanh::lean_dec(v___x_2763_);
                        v___x_2766_ = crate::leanh::lean_box(0);
                        v_isShared_2767_ = v_isSharedCheck_2771_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_2772_ = crate::leanh::lean_ctor_get(v___x_2763_, 0);
                    v_isSharedCheck_2779_ = (!crate::leanh::lean_is_exclusive(v___x_2763_)) as u8;
                    if v_isSharedCheck_2779_ == 0 {
                        v___x_2774_ = v___x_2763_;
                        v_isShared_2775_ = v_isSharedCheck_2779_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_2772_);
                        crate::leanh::lean_dec(v___x_2763_);
                        v___x_2774_ = crate::leanh::lean_box(0);
                        v_isShared_2775_ = v_isSharedCheck_2779_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_2767_ == 0 {
                    v___x_2769_ = v___x_2766_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2770_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2770_, 0, v_a_2764_);
                    v___x_2769_ = v_reuseFailAlloc_2770_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_2769_;
            }
            3 => {
                if v_isShared_2775_ == 0 {
                    v___x_2777_ = v___x_2774_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2778_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2778_, 0, v_a_2772_);
                    v___x_2777_ = v_reuseFailAlloc_2778_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_2777_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Async_System_getTmpDir___boxed(
    mut v_a_2780_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2781_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2781_ = l_Std_Async_System_getTmpDir();
    return v_res_2781_;
}
pub unsafe fn l_Std_Async_System_getCurrentUser() -> *mut crate::leanh::LeanObject {
    let mut v___x_2783_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2784_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2786_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2787_: u8 = 0;
    let mut v_username_2788_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_uid_2789_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_gid_2790_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_shell_2791_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_homedir_2792_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2794_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2795_: u8 = 0;
    let mut v___y_2797_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2798_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2799_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2801_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2803_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2804_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2805_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2807_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2808_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2809_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2810_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2812_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2813_: u8 = 0;
    let mut v___x_2815_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2816_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2817_: u8 = 0;
    let mut v___y_2819_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2820_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2821_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2823_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2824_: u8 = 0;
    let mut v___x_2825_: u64 = 0;
    let mut v___x_2826_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2828_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2829_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2830_: u8 = 0;
    let mut v___x_2831_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2832_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2834_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2835_: u8 = 0;
    let mut v___x_2836_: u64 = 0;
    let mut v___x_2837_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2839_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2840_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2841_: u8 = 0;
    let mut v_isSharedCheck_2842_: u8 = 0;
    let mut v_isSharedCheck_2843_: u8 = 0;
    let mut v_a_2844_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2846_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2847_: u8 = 0;
    let mut v___x_2849_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2850_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2851_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2783_ = lean_uv_os_get_passwd();
                if crate::leanh::lean_obj_tag(v___x_2783_) == 0 {
                    v_a_2784_ = crate::leanh::lean_ctor_get(v___x_2783_, 0);
                    v_isSharedCheck_2843_ = (!crate::leanh::lean_is_exclusive(v___x_2783_)) as u8;
                    if v_isSharedCheck_2843_ == 0 {
                        v___x_2786_ = v___x_2783_;
                        v_isShared_2787_ = v_isSharedCheck_2843_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_2784_);
                        crate::leanh::lean_dec(v___x_2783_);
                        v___x_2786_ = crate::leanh::lean_box(0);
                        v_isShared_2787_ = v_isSharedCheck_2843_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_2844_ = crate::leanh::lean_ctor_get(v___x_2783_, 0);
                    v_isSharedCheck_2851_ = (!crate::leanh::lean_is_exclusive(v___x_2783_)) as u8;
                    if v_isSharedCheck_2851_ == 0 {
                        v___x_2846_ = v___x_2783_;
                        v_isShared_2847_ = v_isSharedCheck_2851_;
                        state = 14;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_2844_);
                        crate::leanh::lean_dec(v___x_2783_);
                        v___x_2846_ = crate::leanh::lean_box(0);
                        v_isShared_2847_ = v_isSharedCheck_2851_;
                        state = 14;
                        continue;
                    }
                }
            }
            1 => {
                v_username_2788_ = crate::leanh::lean_ctor_get(v_a_2784_, 0);
                v_uid_2789_ = crate::leanh::lean_ctor_get(v_a_2784_, 1);
                v_gid_2790_ = crate::leanh::lean_ctor_get(v_a_2784_, 2);
                v_shell_2791_ = crate::leanh::lean_ctor_get(v_a_2784_, 3);
                v_homedir_2792_ = crate::leanh::lean_ctor_get(v_a_2784_, 4);
                v_isSharedCheck_2842_ = (!crate::leanh::lean_is_exclusive(v_a_2784_)) as u8;
                if v_isSharedCheck_2842_ == 0 {
                    v___x_2794_ = v_a_2784_;
                    v_isShared_2795_ = v_isSharedCheck_2842_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_homedir_2792_);
                    crate::leanh::lean_inc(v_shell_2791_);
                    crate::leanh::lean_inc(v_gid_2790_);
                    crate::leanh::lean_inc(v_uid_2789_);
                    crate::leanh::lean_inc(v_username_2788_);
                    crate::leanh::lean_dec(v_a_2784_);
                    v___x_2794_ = crate::leanh::lean_box(0);
                    v_isShared_2795_ = v_isSharedCheck_2842_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                if crate::leanh::lean_obj_tag(v_uid_2789_) == 0 {
                    v___x_2831_ = crate::leanh::lean_box(0);
                    v___y_2819_ = v___x_2831_;
                    state = 9;
                    continue;
                } else {
                    v_val_2832_ = crate::leanh::lean_ctor_get(v_uid_2789_, 0);
                    v_isSharedCheck_2841_ = (!crate::leanh::lean_is_exclusive(v_uid_2789_)) as u8;
                    if v_isSharedCheck_2841_ == 0 {
                        v___x_2834_ = v_uid_2789_;
                        v_isShared_2835_ = v_isSharedCheck_2841_;
                        state = 12;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_val_2832_);
                        crate::leanh::lean_dec(v_uid_2789_);
                        v___x_2834_ = crate::leanh::lean_box(0);
                        v_isShared_2835_ = v_isSharedCheck_2841_;
                        state = 12;
                        continue;
                    }
                }
            }
            3 => {
                if v_isShared_2795_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2794_, 4, v___y_2799_);
                    crate::leanh::lean_ctor_set(v___x_2794_, 2, v___y_2798_);
                    crate::leanh::lean_ctor_set(v___x_2794_, 1, v___y_2797_);
                    v___x_2801_ = v___x_2794_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2805_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2805_, 0, v_username_2788_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2805_, 1, v___y_2797_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2805_, 2, v___y_2798_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2805_, 3, v_shell_2791_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2805_, 4, v___y_2799_);
                    v___x_2801_ = v_reuseFailAlloc_2805_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                if v_isShared_2787_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2786_, 0, v___x_2801_);
                    v___x_2803_ = v___x_2786_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_2804_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2804_, 0, v___x_2801_);
                    v___x_2803_ = v_reuseFailAlloc_2804_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_2803_;
            }
            6 => {
                if crate::leanh::lean_obj_tag(v_homedir_2792_) == 0 {
                    v___x_2809_ = crate::leanh::lean_box(0);
                    v___y_2797_ = v___y_2807_;
                    v___y_2798_ = v___y_2808_;
                    v___y_2799_ = v___x_2809_;
                    state = 3;
                    continue;
                } else {
                    v_val_2810_ = crate::leanh::lean_ctor_get(v_homedir_2792_, 0);
                    v_isSharedCheck_2817_ =
                        (!crate::leanh::lean_is_exclusive(v_homedir_2792_)) as u8;
                    if v_isSharedCheck_2817_ == 0 {
                        v___x_2812_ = v_homedir_2792_;
                        v_isShared_2813_ = v_isSharedCheck_2817_;
                        state = 7;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_val_2810_);
                        crate::leanh::lean_dec(v_homedir_2792_);
                        v___x_2812_ = crate::leanh::lean_box(0);
                        v_isShared_2813_ = v_isSharedCheck_2817_;
                        state = 7;
                        continue;
                    }
                }
            }
            7 => {
                if v_isShared_2813_ == 0 {
                    v___x_2815_ = v___x_2812_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_2816_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2816_, 0, v_val_2810_);
                    v___x_2815_ = v_reuseFailAlloc_2816_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                v___y_2797_ = v___y_2807_;
                v___y_2798_ = v___y_2808_;
                v___y_2799_ = v___x_2815_;
                state = 3;
                continue;
            }
            9 => {
                if crate::leanh::lean_obj_tag(v_gid_2790_) == 0 {
                    v___x_2820_ = crate::leanh::lean_box(0);
                    v___y_2807_ = v___y_2819_;
                    v___y_2808_ = v___x_2820_;
                    state = 6;
                    continue;
                } else {
                    v_val_2821_ = crate::leanh::lean_ctor_get(v_gid_2790_, 0);
                    v_isSharedCheck_2830_ = (!crate::leanh::lean_is_exclusive(v_gid_2790_)) as u8;
                    if v_isSharedCheck_2830_ == 0 {
                        v___x_2823_ = v_gid_2790_;
                        v_isShared_2824_ = v_isSharedCheck_2830_;
                        state = 10;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_val_2821_);
                        crate::leanh::lean_dec(v_gid_2790_);
                        v___x_2823_ = crate::leanh::lean_box(0);
                        v_isShared_2824_ = v_isSharedCheck_2830_;
                        state = 10;
                        continue;
                    }
                }
            }
            10 => {
                v___x_2825_ = crate::leanh::lean_unbox_uint64(v_val_2821_);
                crate::leanh::lean_dec(v_val_2821_);
                v___x_2826_ = lean_uint64_to_nat(v___x_2825_);
                if v_isShared_2824_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2823_, 0, v___x_2826_);
                    v___x_2828_ = v___x_2823_;
                    state = 11;
                    continue;
                } else {
                    v_reuseFailAlloc_2829_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2829_, 0, v___x_2826_);
                    v___x_2828_ = v_reuseFailAlloc_2829_;
                    state = 11;
                    continue;
                }
            }
            11 => {
                v___y_2807_ = v___y_2819_;
                v___y_2808_ = v___x_2828_;
                state = 6;
                continue;
            }
            12 => {
                v___x_2836_ = crate::leanh::lean_unbox_uint64(v_val_2832_);
                crate::leanh::lean_dec(v_val_2832_);
                v___x_2837_ = lean_uint64_to_nat(v___x_2836_);
                if v_isShared_2835_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2834_, 0, v___x_2837_);
                    v___x_2839_ = v___x_2834_;
                    state = 13;
                    continue;
                } else {
                    v_reuseFailAlloc_2840_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2840_, 0, v___x_2837_);
                    v___x_2839_ = v_reuseFailAlloc_2840_;
                    state = 13;
                    continue;
                }
            }
            13 => {
                v___y_2819_ = v___x_2839_;
                state = 9;
                continue;
            }
            14 => {
                if v_isShared_2847_ == 0 {
                    v___x_2849_ = v___x_2846_;
                    state = 15;
                    continue;
                } else {
                    v_reuseFailAlloc_2850_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2850_, 0, v_a_2844_);
                    v___x_2849_ = v_reuseFailAlloc_2850_;
                    state = 15;
                    continue;
                }
            }
            15 => {
                return v___x_2849_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Async_System_getCurrentUser___boxed(
    mut v_a_2852_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2853_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2853_ = l_Std_Async_System_getCurrentUser();
    return v_res_2853_;
}
pub unsafe fn l_Functor_mapRev___at___00Std_Async_System_getGroup_spec__0___redArg(
    mut v_a_2854_: *mut crate::leanh::LeanObject,
    mut v_f_2855_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2856_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2857_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2859_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2860_: u8 = 0;
    let mut v___x_2861_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2863_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2864_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2865_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_a_2854_) == 0 {
                    crate::leanh::lean_dec(v_f_2855_);
                    v___x_2856_ = crate::leanh::lean_box(0);
                    return v___x_2856_;
                } else {
                    v_val_2857_ = crate::leanh::lean_ctor_get(v_a_2854_, 0);
                    v_isSharedCheck_2865_ = (!crate::leanh::lean_is_exclusive(v_a_2854_)) as u8;
                    if v_isSharedCheck_2865_ == 0 {
                        v___x_2859_ = v_a_2854_;
                        v_isShared_2860_ = v_isSharedCheck_2865_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_val_2857_);
                        crate::leanh::lean_dec(v_a_2854_);
                        v___x_2859_ = crate::leanh::lean_box(0);
                        v_isShared_2860_ = v_isSharedCheck_2865_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_2861_ = crate::leanh::lean_apply_1(v_f_2855_, v_val_2857_);
                if v_isShared_2860_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2859_, 0, v___x_2861_);
                    v___x_2863_ = v___x_2859_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2864_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2864_, 0, v___x_2861_);
                    v___x_2863_ = v_reuseFailAlloc_2864_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_2863_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Functor_mapRev___at___00Std_Async_System_getGroup_spec__0(
    mut v_00_u03b1_2866_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_2867_: *mut crate::leanh::LeanObject,
    mut v_a_2868_: *mut crate::leanh::LeanObject,
    mut v_f_2869_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2870_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2870_ =
        l_Functor_mapRev___at___00Std_Async_System_getGroup_spec__0___redArg(v_a_2868_, v_f_2869_);
    return v___x_2870_;
}
pub unsafe fn l_Std_Async_System_getGroup___lam__0(
    mut v_group_2871_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_groupname_2872_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_gid_2873_: u64 = 0;
    let mut v_members_2874_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2875_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2876_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_groupname_2872_ = crate::leanh::lean_ctor_get(v_group_2871_, 0);
    v_gid_2873_ = crate::leanh::lean_ctor_get_uint64(
        v_group_2871_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2) as u32,
    );
    v_members_2874_ = crate::leanh::lean_ctor_get(v_group_2871_, 1);
    v___x_2875_ = lean_uint64_to_nat(v_gid_2873_);
    crate::leanh::lean_inc_ref(v_members_2874_);
    crate::leanh::lean_inc_ref(v_groupname_2872_);
    v___x_2876_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2876_, 0, v_groupname_2872_);
    crate::leanh::lean_ctor_set(v___x_2876_, 1, v___x_2875_);
    crate::leanh::lean_ctor_set(v___x_2876_, 2, v_members_2874_);
    return v___x_2876_;
}
pub unsafe fn l_Std_Async_System_getGroup___lam__0___boxed(
    mut v_group_2877_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2878_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2878_ = l_Std_Async_System_getGroup___lam__0(v_group_2877_);
    crate::leanh::lean_dec_ref(v_group_2877_);
    return v_res_2878_;
}
pub unsafe fn l_Std_Async_System_getGroup(
    mut v_groupId_2880_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2882_: u64 = 0;
    let mut v___x_2883_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2884_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2886_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2887_: u8 = 0;
    let mut v___f_2888_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2889_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2891_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2892_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2893_: u8 = 0;
    let mut v_a_2894_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2896_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2897_: u8 = 0;
    let mut v___x_2899_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2900_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2901_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2882_ = lean_uint64_of_nat(v_groupId_2880_);
                v___x_2883_ = lean_uv_os_get_group(v___x_2882_);
                if crate::leanh::lean_obj_tag(v___x_2883_) == 0 {
                    v_a_2884_ = crate::leanh::lean_ctor_get(v___x_2883_, 0);
                    v_isSharedCheck_2893_ = (!crate::leanh::lean_is_exclusive(v___x_2883_)) as u8;
                    if v_isSharedCheck_2893_ == 0 {
                        v___x_2886_ = v___x_2883_;
                        v_isShared_2887_ = v_isSharedCheck_2893_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_2884_);
                        crate::leanh::lean_dec(v___x_2883_);
                        v___x_2886_ = crate::leanh::lean_box(0);
                        v_isShared_2887_ = v_isSharedCheck_2893_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_2894_ = crate::leanh::lean_ctor_get(v___x_2883_, 0);
                    v_isSharedCheck_2901_ = (!crate::leanh::lean_is_exclusive(v___x_2883_)) as u8;
                    if v_isSharedCheck_2901_ == 0 {
                        v___x_2896_ = v___x_2883_;
                        v_isShared_2897_ = v_isSharedCheck_2901_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_2894_);
                        crate::leanh::lean_dec(v___x_2883_);
                        v___x_2896_ = crate::leanh::lean_box(0);
                        v_isShared_2897_ = v_isSharedCheck_2901_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v___f_2888_ = l_Std_Async_System_getGroup___closed__0;
                v___x_2889_ = l_Functor_mapRev___at___00Std_Async_System_getGroup_spec__0___redArg(
                    v_a_2884_,
                    v___f_2888_,
                );
                if v_isShared_2887_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2886_, 0, v___x_2889_);
                    v___x_2891_ = v___x_2886_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2892_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2892_, 0, v___x_2889_);
                    v___x_2891_ = v_reuseFailAlloc_2892_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_2891_;
            }
            3 => {
                if v_isShared_2897_ == 0 {
                    v___x_2899_ = v___x_2896_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2900_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2900_, 0, v_a_2894_);
                    v___x_2899_ = v_reuseFailAlloc_2900_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_2899_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Async_System_getGroup___boxed(
    mut v_groupId_2902_: *mut crate::leanh::LeanObject,
    mut v_a_2903_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2904_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2904_ = l_Std_Async_System_getGroup(v_groupId_2902_);
    crate::leanh::lean_dec(v_groupId_2902_);
    return v_res_2904_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Std_Async_System(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Std_Time(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Std_Internal_UV_System(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Std_Data_HashMap(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    l_Std_Async_System_instInhabitedGroupId_default =
        _init_l_Std_Async_System_instInhabitedGroupId_default();
    crate::leanh::lean_mark_persistent(l_Std_Async_System_instInhabitedGroupId_default);
    l_Std_Async_System_instInhabitedGroupId = _init_l_Std_Async_System_instInhabitedGroupId();
    crate::leanh::lean_mark_persistent(l_Std_Async_System_instInhabitedGroupId);
    l_Std_Async_System_instInhabitedUserId_default =
        _init_l_Std_Async_System_instInhabitedUserId_default();
    crate::leanh::lean_mark_persistent(l_Std_Async_System_instInhabitedUserId_default);
    l_Std_Async_System_instInhabitedUserId = _init_l_Std_Async_System_instInhabitedUserId();
    crate::leanh::lean_mark_persistent(l_Std_Async_System_instInhabitedUserId);
    l_Std_Async_System_instInhabitedCPUTimes_default =
        _init_l_Std_Async_System_instInhabitedCPUTimes_default();
    crate::leanh::lean_mark_persistent(l_Std_Async_System_instInhabitedCPUTimes_default);
    l_Std_Async_System_instInhabitedCPUTimes = _init_l_Std_Async_System_instInhabitedCPUTimes();
    crate::leanh::lean_mark_persistent(l_Std_Async_System_instInhabitedCPUTimes);
    l_Std_Async_System_instInhabitedCPUInfo_default =
        _init_l_Std_Async_System_instInhabitedCPUInfo_default();
    crate::leanh::lean_mark_persistent(l_Std_Async_System_instInhabitedCPUInfo_default);
    l_Std_Async_System_instInhabitedCPUInfo = _init_l_Std_Async_System_instInhabitedCPUInfo();
    crate::leanh::lean_mark_persistent(l_Std_Async_System_instInhabitedCPUInfo);
    l_Std_Async_System_instInhabitedEnvironment_default =
        _init_l_Std_Async_System_instInhabitedEnvironment_default();
    crate::leanh::lean_mark_persistent(l_Std_Async_System_instInhabitedEnvironment_default);
    l_Std_Async_System_instInhabitedEnvironment =
        _init_l_Std_Async_System_instInhabitedEnvironment();
    crate::leanh::lean_mark_persistent(l_Std_Async_System_instInhabitedEnvironment);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Std_Async_System(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_meta_initialized = true;
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Std_Async_System(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Std_Time(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Std_Internal_UV_System(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Std_Data_HashMap(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Std_Async_System(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Std_Async_System(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Std_Async_System(builtin);
}
