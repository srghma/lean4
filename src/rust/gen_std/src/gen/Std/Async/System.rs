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
pub static mut l_Std_Async_System_instInhabitedGroupId_default: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static mut l_Std_Async_System_instInhabitedGroupId: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Std_Async_System_instOrdGroupId___closed__0_value: leanh::LeanClosureObject<0> =
    leanh::LeanClosureObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut leanh::LeanObject>() * 0)
                as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Std_Async_System_instOrdGroupId_ord___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Std_Async_System_instOrdGroupId___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Async_System_instOrdGroupId___closed__0_value)
        as *mut leanh::LeanObject;
pub static mut l_Std_Async_System_instOrdGroupId: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Async_System_instOrdGroupId___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Std_Async_System_instReprGroupId___lam__0___closed__0_value:
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
    m_data: [71, 114, 111, 117, 112, 73, 100, 46, 109, 107, 32, 0],
};
static mut l_Std_Async_System_instReprGroupId___lam__0___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Async_System_instReprGroupId___lam__0___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Std_Async_System_instReprGroupId___lam__0___closed__1_value:
    leanh::LeanCtorObject<1> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [
        core::ptr::addr_of!(l_Std_Async_System_instReprGroupId___lam__0___closed__0_value)
            as *mut leanh::LeanObject,
    ],
};
static mut l_Std_Async_System_instReprGroupId___lam__0___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Async_System_instReprGroupId___lam__0___closed__1_value)
        as *mut leanh::LeanObject;
pub static l_Std_Async_System_instReprGroupId___closed__0_value: leanh::LeanClosureObject<
    0,
> = leanh::LeanClosureObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut leanh::LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Std_Async_System_instReprGroupId___lam__0___boxed as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Std_Async_System_instReprGroupId___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Async_System_instReprGroupId___closed__0_value)
        as *mut leanh::LeanObject;
pub static mut l_Std_Async_System_instReprGroupId: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Async_System_instReprGroupId___closed__0_value)
        as *mut leanh::LeanObject;
pub static mut l_Std_Async_System_instInhabitedUserId_default: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static mut l_Std_Async_System_instInhabitedUserId: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Std_Async_System_instOrdUserId___closed__0_value: leanh::LeanClosureObject<0> =
    leanh::LeanClosureObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut leanh::LeanObject>() * 0)
                as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Std_Async_System_instOrdUserId_ord___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Std_Async_System_instOrdUserId___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Async_System_instOrdUserId___closed__0_value)
        as *mut leanh::LeanObject;
pub static mut l_Std_Async_System_instOrdUserId: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Async_System_instOrdUserId___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Std_Async_System_instReprUserId___lam__0___closed__0_value:
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
    m_data: [85, 115, 101, 114, 73, 100, 46, 109, 107, 32, 0],
};
static mut l_Std_Async_System_instReprUserId___lam__0___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Async_System_instReprUserId___lam__0___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Std_Async_System_instReprUserId___lam__0___closed__1_value:
    leanh::LeanCtorObject<1> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [
        core::ptr::addr_of!(l_Std_Async_System_instReprUserId___lam__0___closed__0_value)
            as *mut leanh::LeanObject,
    ],
};
static mut l_Std_Async_System_instReprUserId___lam__0___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Async_System_instReprUserId___lam__0___closed__1_value)
        as *mut leanh::LeanObject;
pub static l_Std_Async_System_instReprUserId___closed__0_value: leanh::LeanClosureObject<0> =
    leanh::LeanClosureObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut leanh::LeanObject>() * 0)
                as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Std_Async_System_instReprUserId___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Std_Async_System_instReprUserId___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Async_System_instReprUserId___closed__0_value)
        as *mut leanh::LeanObject;
pub static mut l_Std_Async_System_instReprUserId: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Async_System_instReprUserId___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Std_Async_System_instInhabitedSystemUser_default___closed__0_value:
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
static mut l_Std_Async_System_instInhabitedSystemUser_default___closed__0:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Async_System_instInhabitedSystemUser_default___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Std_Async_System_instInhabitedSystemUser_default___closed__1_value:
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
        core::ptr::addr_of!(l_Std_Async_System_instInhabitedSystemUser_default___closed__0_value)
            as *mut leanh::LeanObject,
        (((0 as usize) << 1) | 1) as *mut leanh::LeanObject,
        (((0 as usize) << 1) | 1) as *mut leanh::LeanObject,
        (((0 as usize) << 1) | 1) as *mut leanh::LeanObject,
        (((0 as usize) << 1) | 1) as *mut leanh::LeanObject,
    ],
};
static mut l_Std_Async_System_instInhabitedSystemUser_default___closed__1:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Async_System_instInhabitedSystemUser_default___closed__1_value)
        as *mut leanh::LeanObject;
pub static mut l_Std_Async_System_instInhabitedSystemUser_default: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Async_System_instInhabitedSystemUser_default___closed__1_value)
        as *mut leanh::LeanObject;
pub static mut l_Std_Async_System_instInhabitedSystemUser: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Async_System_instInhabitedSystemUser_default___closed__1_value)
        as *mut leanh::LeanObject;
pub static l_Option_repr___at___00Std_Async_System_instReprSystemUser_repr_spec__0___closed__0_value: leanh::LeanStringObject<5> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [110, 111, 110, 101, 0]};
static mut l_Option_repr___at___00Std_Async_System_instReprSystemUser_repr_spec__0___closed__0:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Option_repr___at___00Std_Async_System_instReprSystemUser_repr_spec__0___closed__0_value
) as *mut leanh::LeanObject;
pub static l_Option_repr___at___00Std_Async_System_instReprSystemUser_repr_spec__0___closed__1_value: leanh::LeanCtorObject<1> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 3 }, m_objs: [core::ptr::addr_of!(l_Option_repr___at___00Std_Async_System_instReprSystemUser_repr_spec__0___closed__0_value) as *mut leanh::LeanObject] };
static mut l_Option_repr___at___00Std_Async_System_instReprSystemUser_repr_spec__0___closed__1:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Option_repr___at___00Std_Async_System_instReprSystemUser_repr_spec__0___closed__1_value
) as *mut leanh::LeanObject;
pub static l_Option_repr___at___00Std_Async_System_instReprSystemUser_repr_spec__0___closed__2_value: leanh::LeanStringObject<6> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [115, 111, 109, 101, 32, 0]};
static mut l_Option_repr___at___00Std_Async_System_instReprSystemUser_repr_spec__0___closed__2:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Option_repr___at___00Std_Async_System_instReprSystemUser_repr_spec__0___closed__2_value
) as *mut leanh::LeanObject;
pub static l_Option_repr___at___00Std_Async_System_instReprSystemUser_repr_spec__0___closed__3_value: leanh::LeanCtorObject<1> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 3 }, m_objs: [core::ptr::addr_of!(l_Option_repr___at___00Std_Async_System_instReprSystemUser_repr_spec__0___closed__2_value) as *mut leanh::LeanObject] };
static mut l_Option_repr___at___00Std_Async_System_instReprSystemUser_repr_spec__0___closed__3:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Option_repr___at___00Std_Async_System_instReprSystemUser_repr_spec__0___closed__3_value
) as *mut leanh::LeanObject;
pub static l_Option_repr___at___00Std_Async_System_instReprSystemUser_repr_spec__3___closed__0_value: leanh::LeanStringObject<13> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 13, m_capacity: 13, m_length: 12, m_data: [70, 105, 108, 101, 80, 97, 116, 104, 46, 109, 107, 32, 0]};
static mut l_Option_repr___at___00Std_Async_System_instReprSystemUser_repr_spec__3___closed__0:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Option_repr___at___00Std_Async_System_instReprSystemUser_repr_spec__3___closed__0_value
) as *mut leanh::LeanObject;
pub static l_Option_repr___at___00Std_Async_System_instReprSystemUser_repr_spec__3___closed__1_value: leanh::LeanCtorObject<1> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 3 }, m_objs: [core::ptr::addr_of!(l_Option_repr___at___00Std_Async_System_instReprSystemUser_repr_spec__3___closed__0_value) as *mut leanh::LeanObject] };
static mut l_Option_repr___at___00Std_Async_System_instReprSystemUser_repr_spec__3___closed__1:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Option_repr___at___00Std_Async_System_instReprSystemUser_repr_spec__3___closed__1_value
) as *mut leanh::LeanObject;
pub static l_Std_Async_System_instReprSystemUser_repr___redArg___closed__0_value:
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
static mut l_Std_Async_System_instReprSystemUser_repr___redArg___closed__0:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Async_System_instReprSystemUser_repr___redArg___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Std_Async_System_instReprSystemUser_repr___redArg___closed__1_value:
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
static mut l_Std_Async_System_instReprSystemUser_repr___redArg___closed__1:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Async_System_instReprSystemUser_repr___redArg___closed__1_value)
        as *mut leanh::LeanObject;
pub static l_Std_Async_System_instReprSystemUser_repr___redArg___closed__2_value:
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
        l_Std_Async_System_instReprSystemUser_repr___redArg___closed__1_value
    ) as *mut leanh::LeanObject],
};
static mut l_Std_Async_System_instReprSystemUser_repr___redArg___closed__2:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Async_System_instReprSystemUser_repr___redArg___closed__2_value)
        as *mut leanh::LeanObject;
pub static l_Std_Async_System_instReprSystemUser_repr___redArg___closed__3_value:
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
        core::ptr::addr_of!(l_Std_Async_System_instReprSystemUser_repr___redArg___closed__2_value)
            as *mut leanh::LeanObject,
    ],
};
static mut l_Std_Async_System_instReprSystemUser_repr___redArg___closed__3:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Async_System_instReprSystemUser_repr___redArg___closed__3_value)
        as *mut leanh::LeanObject;
pub static l_Std_Async_System_instReprSystemUser_repr___redArg___closed__4_value:
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
static mut l_Std_Async_System_instReprSystemUser_repr___redArg___closed__4:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Async_System_instReprSystemUser_repr___redArg___closed__4_value)
        as *mut leanh::LeanObject;
pub static l_Std_Async_System_instReprSystemUser_repr___redArg___closed__5_value:
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
        l_Std_Async_System_instReprSystemUser_repr___redArg___closed__4_value
    ) as *mut leanh::LeanObject],
};
static mut l_Std_Async_System_instReprSystemUser_repr___redArg___closed__5:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Async_System_instReprSystemUser_repr___redArg___closed__5_value)
        as *mut leanh::LeanObject;
pub static l_Std_Async_System_instReprSystemUser_repr___redArg___closed__6_value:
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
        core::ptr::addr_of!(l_Std_Async_System_instReprSystemUser_repr___redArg___closed__3_value)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Std_Async_System_instReprSystemUser_repr___redArg___closed__5_value)
            as *mut leanh::LeanObject,
    ],
};
static mut l_Std_Async_System_instReprSystemUser_repr___redArg___closed__6:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Async_System_instReprSystemUser_repr___redArg___closed__6_value)
        as *mut leanh::LeanObject;
static mut l_Std_Async_System_instReprSystemUser_repr___redArg___closed__7_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_Async_System_instReprSystemUser_repr___redArg___closed__7:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Std_Async_System_instReprSystemUser_repr___redArg___closed__8_value:
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
static mut l_Std_Async_System_instReprSystemUser_repr___redArg___closed__8:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Async_System_instReprSystemUser_repr___redArg___closed__8_value)
        as *mut leanh::LeanObject;
pub static l_Std_Async_System_instReprSystemUser_repr___redArg___closed__9_value:
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
        l_Std_Async_System_instReprSystemUser_repr___redArg___closed__8_value
    ) as *mut leanh::LeanObject],
};
static mut l_Std_Async_System_instReprSystemUser_repr___redArg___closed__9:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Async_System_instReprSystemUser_repr___redArg___closed__9_value)
        as *mut leanh::LeanObject;
pub static l_Std_Async_System_instReprSystemUser_repr___redArg___closed__10_value:
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
    m_data: [117, 115, 101, 114, 73, 100, 0],
};
static mut l_Std_Async_System_instReprSystemUser_repr___redArg___closed__10:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Async_System_instReprSystemUser_repr___redArg___closed__10_value)
        as *mut leanh::LeanObject;
pub static l_Std_Async_System_instReprSystemUser_repr___redArg___closed__11_value:
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
        l_Std_Async_System_instReprSystemUser_repr___redArg___closed__10_value
    ) as *mut leanh::LeanObject],
};
static mut l_Std_Async_System_instReprSystemUser_repr___redArg___closed__11:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Async_System_instReprSystemUser_repr___redArg___closed__11_value)
        as *mut leanh::LeanObject;
static mut l_Std_Async_System_instReprSystemUser_repr___redArg___closed__12_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_Async_System_instReprSystemUser_repr___redArg___closed__12:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Std_Async_System_instReprSystemUser_repr___redArg___closed__13_value:
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
    m_data: [103, 114, 111, 117, 112, 73, 100, 0],
};
static mut l_Std_Async_System_instReprSystemUser_repr___redArg___closed__13:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Async_System_instReprSystemUser_repr___redArg___closed__13_value)
        as *mut leanh::LeanObject;
pub static l_Std_Async_System_instReprSystemUser_repr___redArg___closed__14_value:
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
        l_Std_Async_System_instReprSystemUser_repr___redArg___closed__13_value
    ) as *mut leanh::LeanObject],
};
static mut l_Std_Async_System_instReprSystemUser_repr___redArg___closed__14:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Async_System_instReprSystemUser_repr___redArg___closed__14_value)
        as *mut leanh::LeanObject;
static mut l_Std_Async_System_instReprSystemUser_repr___redArg___closed__15_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_Async_System_instReprSystemUser_repr___redArg___closed__15:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Std_Async_System_instReprSystemUser_repr___redArg___closed__16_value:
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
static mut l_Std_Async_System_instReprSystemUser_repr___redArg___closed__16:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Async_System_instReprSystemUser_repr___redArg___closed__16_value)
        as *mut leanh::LeanObject;
pub static l_Std_Async_System_instReprSystemUser_repr___redArg___closed__17_value:
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
        l_Std_Async_System_instReprSystemUser_repr___redArg___closed__16_value
    ) as *mut leanh::LeanObject],
};
static mut l_Std_Async_System_instReprSystemUser_repr___redArg___closed__17:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Async_System_instReprSystemUser_repr___redArg___closed__17_value)
        as *mut leanh::LeanObject;
static mut l_Std_Async_System_instReprSystemUser_repr___redArg___closed__18_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_Async_System_instReprSystemUser_repr___redArg___closed__18:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Std_Async_System_instReprSystemUser_repr___redArg___closed__19_value:
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
    m_data: [104, 111, 109, 101, 68, 105, 114, 0],
};
static mut l_Std_Async_System_instReprSystemUser_repr___redArg___closed__19:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Async_System_instReprSystemUser_repr___redArg___closed__19_value)
        as *mut leanh::LeanObject;
pub static l_Std_Async_System_instReprSystemUser_repr___redArg___closed__20_value:
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
        l_Std_Async_System_instReprSystemUser_repr___redArg___closed__19_value
    ) as *mut leanh::LeanObject],
};
static mut l_Std_Async_System_instReprSystemUser_repr___redArg___closed__20:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Async_System_instReprSystemUser_repr___redArg___closed__20_value)
        as *mut leanh::LeanObject;
pub static l_Std_Async_System_instReprSystemUser_repr___redArg___closed__21_value:
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
static mut l_Std_Async_System_instReprSystemUser_repr___redArg___closed__21:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Async_System_instReprSystemUser_repr___redArg___closed__21_value)
        as *mut leanh::LeanObject;
static mut l_Std_Async_System_instReprSystemUser_repr___redArg___closed__22_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_Async_System_instReprSystemUser_repr___redArg___closed__22:
    *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Std_Async_System_instReprSystemUser_repr___redArg___closed__23_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_Async_System_instReprSystemUser_repr___redArg___closed__23:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Std_Async_System_instReprSystemUser_repr___redArg___closed__24_value:
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
        l_Std_Async_System_instReprSystemUser_repr___redArg___closed__0_value
    ) as *mut leanh::LeanObject],
};
static mut l_Std_Async_System_instReprSystemUser_repr___redArg___closed__24:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Async_System_instReprSystemUser_repr___redArg___closed__24_value)
        as *mut leanh::LeanObject;
pub static l_Std_Async_System_instReprSystemUser_repr___redArg___closed__25_value:
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
        l_Std_Async_System_instReprSystemUser_repr___redArg___closed__21_value
    ) as *mut leanh::LeanObject],
};
static mut l_Std_Async_System_instReprSystemUser_repr___redArg___closed__25:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Async_System_instReprSystemUser_repr___redArg___closed__25_value)
        as *mut leanh::LeanObject;
pub static l_Std_Async_System_instReprSystemUser___closed__0_value:
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
    m_fun: l_Std_Async_System_instReprSystemUser_repr___boxed as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Std_Async_System_instReprSystemUser___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Async_System_instReprSystemUser___closed__0_value)
        as *mut leanh::LeanObject;
pub static mut l_Std_Async_System_instReprSystemUser: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Async_System_instReprSystemUser___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Array_repr___at___00Std_Async_System_instReprGroupInfo_repr_spec__0___closed__0_value: leanh::LeanStringObject<3> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 3, m_capacity: 3, m_length: 2, m_data: [35, 91, 0]};
static mut l_Array_repr___at___00Std_Async_System_instReprGroupInfo_repr_spec__0___closed__0:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Array_repr___at___00Std_Async_System_instReprGroupInfo_repr_spec__0___closed__0_value
) as *mut leanh::LeanObject;
pub static l_Array_repr___at___00Std_Async_System_instReprGroupInfo_repr_spec__0___closed__1_value: leanh::LeanCtorObject<2> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 5 }, m_objs: [core::ptr::addr_of!(l_Std_Async_System_instReprSystemUser_repr___redArg___closed__9_value) as *mut leanh::LeanObject,((( 1 as usize) << 1) | 1) as *mut leanh::LeanObject] };
static mut l_Array_repr___at___00Std_Async_System_instReprGroupInfo_repr_spec__0___closed__1:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Array_repr___at___00Std_Async_System_instReprGroupInfo_repr_spec__0___closed__1_value
) as *mut leanh::LeanObject;
pub static l_Array_repr___at___00Std_Async_System_instReprGroupInfo_repr_spec__0___closed__2_value: leanh::LeanStringObject<2> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [93, 0]};
static mut l_Array_repr___at___00Std_Async_System_instReprGroupInfo_repr_spec__0___closed__2:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Array_repr___at___00Std_Async_System_instReprGroupInfo_repr_spec__0___closed__2_value
) as *mut leanh::LeanObject;
static mut l_Array_repr___at___00Std_Async_System_instReprGroupInfo_repr_spec__0___closed__3_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Array_repr___at___00Std_Async_System_instReprGroupInfo_repr_spec__0___closed__3:
    *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Array_repr___at___00Std_Async_System_instReprGroupInfo_repr_spec__0___closed__4_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Array_repr___at___00Std_Async_System_instReprGroupInfo_repr_spec__0___closed__4:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Array_repr___at___00Std_Async_System_instReprGroupInfo_repr_spec__0___closed__5_value: leanh::LeanCtorObject<1> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 3 }, m_objs: [core::ptr::addr_of!(l_Array_repr___at___00Std_Async_System_instReprGroupInfo_repr_spec__0___closed__0_value) as *mut leanh::LeanObject] };
static mut l_Array_repr___at___00Std_Async_System_instReprGroupInfo_repr_spec__0___closed__5:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Array_repr___at___00Std_Async_System_instReprGroupInfo_repr_spec__0___closed__5_value
) as *mut leanh::LeanObject;
pub static l_Array_repr___at___00Std_Async_System_instReprGroupInfo_repr_spec__0___closed__6_value: leanh::LeanCtorObject<1> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 3 }, m_objs: [core::ptr::addr_of!(l_Array_repr___at___00Std_Async_System_instReprGroupInfo_repr_spec__0___closed__2_value) as *mut leanh::LeanObject] };
static mut l_Array_repr___at___00Std_Async_System_instReprGroupInfo_repr_spec__0___closed__6:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Array_repr___at___00Std_Async_System_instReprGroupInfo_repr_spec__0___closed__6_value
) as *mut leanh::LeanObject;
pub static l_Array_repr___at___00Std_Async_System_instReprGroupInfo_repr_spec__0___closed__7_value: leanh::LeanStringObject<4> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 4, m_capacity: 4, m_length: 3, m_data: [35, 91, 93, 0]};
static mut l_Array_repr___at___00Std_Async_System_instReprGroupInfo_repr_spec__0___closed__7:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Array_repr___at___00Std_Async_System_instReprGroupInfo_repr_spec__0___closed__7_value
) as *mut leanh::LeanObject;
pub static l_Array_repr___at___00Std_Async_System_instReprGroupInfo_repr_spec__0___closed__8_value: leanh::LeanCtorObject<1> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 3 }, m_objs: [core::ptr::addr_of!(l_Array_repr___at___00Std_Async_System_instReprGroupInfo_repr_spec__0___closed__7_value) as *mut leanh::LeanObject] };
static mut l_Array_repr___at___00Std_Async_System_instReprGroupInfo_repr_spec__0___closed__8:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Array_repr___at___00Std_Async_System_instReprGroupInfo_repr_spec__0___closed__8_value
) as *mut leanh::LeanObject;
pub static l_Std_Async_System_instReprGroupInfo_repr___redArg___closed__0_value:
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
    m_data: [103, 114, 111, 117, 112, 78, 97, 109, 101, 0],
};
static mut l_Std_Async_System_instReprGroupInfo_repr___redArg___closed__0:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Async_System_instReprGroupInfo_repr___redArg___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Std_Async_System_instReprGroupInfo_repr___redArg___closed__1_value:
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
        l_Std_Async_System_instReprGroupInfo_repr___redArg___closed__0_value
    ) as *mut leanh::LeanObject],
};
static mut l_Std_Async_System_instReprGroupInfo_repr___redArg___closed__1:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Async_System_instReprGroupInfo_repr___redArg___closed__1_value)
        as *mut leanh::LeanObject;
pub static l_Std_Async_System_instReprGroupInfo_repr___redArg___closed__2_value:
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
        core::ptr::addr_of!(l_Std_Async_System_instReprGroupInfo_repr___redArg___closed__1_value)
            as *mut leanh::LeanObject,
    ],
};
static mut l_Std_Async_System_instReprGroupInfo_repr___redArg___closed__2:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Async_System_instReprGroupInfo_repr___redArg___closed__2_value)
        as *mut leanh::LeanObject;
pub static l_Std_Async_System_instReprGroupInfo_repr___redArg___closed__3_value:
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
        core::ptr::addr_of!(l_Std_Async_System_instReprGroupInfo_repr___redArg___closed__2_value)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Std_Async_System_instReprSystemUser_repr___redArg___closed__5_value)
            as *mut leanh::LeanObject,
    ],
};
static mut l_Std_Async_System_instReprGroupInfo_repr___redArg___closed__3:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Async_System_instReprGroupInfo_repr___redArg___closed__3_value)
        as *mut leanh::LeanObject;
static mut l_Std_Async_System_instReprGroupInfo_repr___redArg___closed__4_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_Async_System_instReprGroupInfo_repr___redArg___closed__4:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Std_Async_System_instReprGroupInfo_repr___redArg___closed__5_value:
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
static mut l_Std_Async_System_instReprGroupInfo_repr___redArg___closed__5:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Async_System_instReprGroupInfo_repr___redArg___closed__5_value)
        as *mut leanh::LeanObject;
pub static l_Std_Async_System_instReprGroupInfo_repr___redArg___closed__6_value:
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
        l_Std_Async_System_instReprGroupInfo_repr___redArg___closed__5_value
    ) as *mut leanh::LeanObject],
};
static mut l_Std_Async_System_instReprGroupInfo_repr___redArg___closed__6:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Async_System_instReprGroupInfo_repr___redArg___closed__6_value)
        as *mut leanh::LeanObject;
pub static l_Std_Async_System_instReprGroupInfo___closed__0_value: leanh::LeanClosureObject<
    0,
> = leanh::LeanClosureObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut leanh::LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Std_Async_System_instReprGroupInfo_repr___boxed as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Std_Async_System_instReprGroupInfo___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Async_System_instReprGroupInfo___closed__0_value)
        as *mut leanh::LeanObject;
pub static mut l_Std_Async_System_instReprGroupInfo: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Async_System_instReprGroupInfo___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Std_Async_System_instInhabitedGroupInfo_default___closed__0_value:
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
static mut l_Std_Async_System_instInhabitedGroupInfo_default___closed__0:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Async_System_instInhabitedGroupInfo_default___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Std_Async_System_instInhabitedGroupInfo_default___closed__1_value:
    leanh::LeanCtorObject<3> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 3
            + 0) as u16,
        other: 3,
        tag: 0,
    },
    m_objs: [
        core::ptr::addr_of!(l_Std_Async_System_instInhabitedSystemUser_default___closed__0_value)
            as *mut leanh::LeanObject,
        (((0 as usize) << 1) | 1) as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Std_Async_System_instInhabitedGroupInfo_default___closed__0_value)
            as *mut leanh::LeanObject,
    ],
};
static mut l_Std_Async_System_instInhabitedGroupInfo_default___closed__1:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Async_System_instInhabitedGroupInfo_default___closed__1_value)
        as *mut leanh::LeanObject;
pub static mut l_Std_Async_System_instInhabitedGroupInfo_default: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Async_System_instInhabitedGroupInfo_default___closed__1_value)
        as *mut leanh::LeanObject;
pub static mut l_Std_Async_System_instInhabitedGroupInfo: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Async_System_instInhabitedGroupInfo_default___closed__1_value)
        as *mut leanh::LeanObject;
static mut l_Std_Async_System_instInhabitedCPUTimes_default___closed__0_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_Async_System_instInhabitedCPUTimes_default___closed__0:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static mut l_Std_Async_System_instInhabitedCPUTimes_default: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static mut l_Std_Async_System_instInhabitedCPUTimes: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Std_Async_System_instReprCPUTimes_repr___redArg___closed__0_value:
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
static mut l_Std_Async_System_instReprCPUTimes_repr___redArg___closed__0:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Async_System_instReprCPUTimes_repr___redArg___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Std_Async_System_instReprCPUTimes_repr___redArg___closed__1_value:
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
        l_Std_Async_System_instReprCPUTimes_repr___redArg___closed__0_value
    ) as *mut leanh::LeanObject],
};
static mut l_Std_Async_System_instReprCPUTimes_repr___redArg___closed__1:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Async_System_instReprCPUTimes_repr___redArg___closed__1_value)
        as *mut leanh::LeanObject;
pub static l_Std_Async_System_instReprCPUTimes_repr___redArg___closed__2_value:
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
        core::ptr::addr_of!(l_Std_Async_System_instReprCPUTimes_repr___redArg___closed__1_value)
            as *mut leanh::LeanObject,
    ],
};
static mut l_Std_Async_System_instReprCPUTimes_repr___redArg___closed__2:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Async_System_instReprCPUTimes_repr___redArg___closed__2_value)
        as *mut leanh::LeanObject;
pub static l_Std_Async_System_instReprCPUTimes_repr___redArg___closed__3_value:
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
        core::ptr::addr_of!(l_Std_Async_System_instReprCPUTimes_repr___redArg___closed__2_value)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Std_Async_System_instReprSystemUser_repr___redArg___closed__5_value)
            as *mut leanh::LeanObject,
    ],
};
static mut l_Std_Async_System_instReprCPUTimes_repr___redArg___closed__3:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Async_System_instReprCPUTimes_repr___redArg___closed__3_value)
        as *mut leanh::LeanObject;
pub static l_Std_Async_System_instReprCPUTimes_repr___redArg___closed__4_value:
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
    m_data: [110, 105, 99, 101, 84, 105, 109, 101, 0],
};
static mut l_Std_Async_System_instReprCPUTimes_repr___redArg___closed__4:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Async_System_instReprCPUTimes_repr___redArg___closed__4_value)
        as *mut leanh::LeanObject;
pub static l_Std_Async_System_instReprCPUTimes_repr___redArg___closed__5_value:
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
        l_Std_Async_System_instReprCPUTimes_repr___redArg___closed__4_value
    ) as *mut leanh::LeanObject],
};
static mut l_Std_Async_System_instReprCPUTimes_repr___redArg___closed__5:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Async_System_instReprCPUTimes_repr___redArg___closed__5_value)
        as *mut leanh::LeanObject;
pub static l_Std_Async_System_instReprCPUTimes_repr___redArg___closed__6_value:
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
static mut l_Std_Async_System_instReprCPUTimes_repr___redArg___closed__6:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Async_System_instReprCPUTimes_repr___redArg___closed__6_value)
        as *mut leanh::LeanObject;
pub static l_Std_Async_System_instReprCPUTimes_repr___redArg___closed__7_value:
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
        l_Std_Async_System_instReprCPUTimes_repr___redArg___closed__6_value
    ) as *mut leanh::LeanObject],
};
static mut l_Std_Async_System_instReprCPUTimes_repr___redArg___closed__7:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Async_System_instReprCPUTimes_repr___redArg___closed__7_value)
        as *mut leanh::LeanObject;
static mut l_Std_Async_System_instReprCPUTimes_repr___redArg___closed__8_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_Async_System_instReprCPUTimes_repr___redArg___closed__8:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Std_Async_System_instReprCPUTimes_repr___redArg___closed__9_value:
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
    m_data: [105, 100, 108, 101, 84, 105, 109, 101, 0],
};
static mut l_Std_Async_System_instReprCPUTimes_repr___redArg___closed__9:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Async_System_instReprCPUTimes_repr___redArg___closed__9_value)
        as *mut leanh::LeanObject;
pub static l_Std_Async_System_instReprCPUTimes_repr___redArg___closed__10_value:
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
        l_Std_Async_System_instReprCPUTimes_repr___redArg___closed__9_value
    ) as *mut leanh::LeanObject],
};
static mut l_Std_Async_System_instReprCPUTimes_repr___redArg___closed__10:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Async_System_instReprCPUTimes_repr___redArg___closed__10_value)
        as *mut leanh::LeanObject;
pub static l_Std_Async_System_instReprCPUTimes_repr___redArg___closed__11_value:
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
        105, 110, 116, 101, 114, 114, 117, 112, 116, 84, 105, 109, 101, 0,
    ],
};
static mut l_Std_Async_System_instReprCPUTimes_repr___redArg___closed__11:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Async_System_instReprCPUTimes_repr___redArg___closed__11_value)
        as *mut leanh::LeanObject;
pub static l_Std_Async_System_instReprCPUTimes_repr___redArg___closed__12_value:
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
        l_Std_Async_System_instReprCPUTimes_repr___redArg___closed__11_value
    ) as *mut leanh::LeanObject],
};
static mut l_Std_Async_System_instReprCPUTimes_repr___redArg___closed__12:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Async_System_instReprCPUTimes_repr___redArg___closed__12_value)
        as *mut leanh::LeanObject;
static mut l_Std_Async_System_instReprCPUTimes_repr___redArg___closed__13_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_Async_System_instReprCPUTimes_repr___redArg___closed__13:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Std_Async_System_instReprCPUTimes___closed__0_value: leanh::LeanClosureObject<
    0,
> = leanh::LeanClosureObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut leanh::LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Std_Async_System_instReprCPUTimes_repr___boxed as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Std_Async_System_instReprCPUTimes___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Async_System_instReprCPUTimes___closed__0_value)
        as *mut leanh::LeanObject;
pub static mut l_Std_Async_System_instReprCPUTimes: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Async_System_instReprCPUTimes___closed__0_value)
        as *mut leanh::LeanObject;
static mut l_Std_Async_System_instInhabitedCPUInfo_default___closed__0_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_Async_System_instInhabitedCPUInfo_default___closed__0:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static mut l_Std_Async_System_instInhabitedCPUInfo_default: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static mut l_Std_Async_System_instInhabitedCPUInfo: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Std_Async_System_instReprCPUInfo_repr___redArg___closed__0_value:
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
static mut l_Std_Async_System_instReprCPUInfo_repr___redArg___closed__0:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Async_System_instReprCPUInfo_repr___redArg___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Std_Async_System_instReprCPUInfo_repr___redArg___closed__1_value:
    leanh::LeanCtorObject<1> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [
        core::ptr::addr_of!(l_Std_Async_System_instReprCPUInfo_repr___redArg___closed__0_value)
            as *mut leanh::LeanObject,
    ],
};
static mut l_Std_Async_System_instReprCPUInfo_repr___redArg___closed__1:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Async_System_instReprCPUInfo_repr___redArg___closed__1_value)
        as *mut leanh::LeanObject;
pub static l_Std_Async_System_instReprCPUInfo_repr___redArg___closed__2_value:
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
        core::ptr::addr_of!(l_Std_Async_System_instReprCPUInfo_repr___redArg___closed__1_value)
            as *mut leanh::LeanObject,
    ],
};
static mut l_Std_Async_System_instReprCPUInfo_repr___redArg___closed__2:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Async_System_instReprCPUInfo_repr___redArg___closed__2_value)
        as *mut leanh::LeanObject;
pub static l_Std_Async_System_instReprCPUInfo_repr___redArg___closed__3_value:
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
        core::ptr::addr_of!(l_Std_Async_System_instReprCPUInfo_repr___redArg___closed__2_value)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Std_Async_System_instReprSystemUser_repr___redArg___closed__5_value)
            as *mut leanh::LeanObject,
    ],
};
static mut l_Std_Async_System_instReprCPUInfo_repr___redArg___closed__3:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Async_System_instReprCPUInfo_repr___redArg___closed__3_value)
        as *mut leanh::LeanObject;
pub static l_Std_Async_System_instReprCPUInfo_repr___redArg___closed__4_value:
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
static mut l_Std_Async_System_instReprCPUInfo_repr___redArg___closed__4:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Async_System_instReprCPUInfo_repr___redArg___closed__4_value)
        as *mut leanh::LeanObject;
pub static l_Std_Async_System_instReprCPUInfo_repr___redArg___closed__5_value:
    leanh::LeanCtorObject<1> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [
        core::ptr::addr_of!(l_Std_Async_System_instReprCPUInfo_repr___redArg___closed__4_value)
            as *mut leanh::LeanObject,
    ],
};
static mut l_Std_Async_System_instReprCPUInfo_repr___redArg___closed__5:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Async_System_instReprCPUInfo_repr___redArg___closed__5_value)
        as *mut leanh::LeanObject;
pub static l_Std_Async_System_instReprCPUInfo_repr___redArg___closed__6_value:
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
static mut l_Std_Async_System_instReprCPUInfo_repr___redArg___closed__6:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Async_System_instReprCPUInfo_repr___redArg___closed__6_value)
        as *mut leanh::LeanObject;
pub static l_Std_Async_System_instReprCPUInfo_repr___redArg___closed__7_value:
    leanh::LeanCtorObject<1> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [
        core::ptr::addr_of!(l_Std_Async_System_instReprCPUInfo_repr___redArg___closed__6_value)
            as *mut leanh::LeanObject,
    ],
};
static mut l_Std_Async_System_instReprCPUInfo_repr___redArg___closed__7:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Async_System_instReprCPUInfo_repr___redArg___closed__7_value)
        as *mut leanh::LeanObject;
pub static l_Std_Async_System_instReprCPUInfo___closed__0_value: leanh::LeanClosureObject<
    0,
> = leanh::LeanClosureObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut leanh::LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Std_Async_System_instReprCPUInfo_repr___boxed as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Std_Async_System_instReprCPUInfo___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Async_System_instReprCPUInfo___closed__0_value)
        as *mut leanh::LeanObject;
pub static mut l_Std_Async_System_instReprCPUInfo: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Async_System_instReprCPUInfo___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Std_Async_System_instReprOSInfo_repr___redArg___closed__0_value:
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
    m_data: [110, 97, 109, 101, 0],
};
static mut l_Std_Async_System_instReprOSInfo_repr___redArg___closed__0:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Async_System_instReprOSInfo_repr___redArg___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Std_Async_System_instReprOSInfo_repr___redArg___closed__1_value:
    leanh::LeanCtorObject<1> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [
        core::ptr::addr_of!(l_Std_Async_System_instReprOSInfo_repr___redArg___closed__0_value)
            as *mut leanh::LeanObject,
    ],
};
static mut l_Std_Async_System_instReprOSInfo_repr___redArg___closed__1:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Async_System_instReprOSInfo_repr___redArg___closed__1_value)
        as *mut leanh::LeanObject;
pub static l_Std_Async_System_instReprOSInfo_repr___redArg___closed__2_value:
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
        core::ptr::addr_of!(l_Std_Async_System_instReprOSInfo_repr___redArg___closed__1_value)
            as *mut leanh::LeanObject,
    ],
};
static mut l_Std_Async_System_instReprOSInfo_repr___redArg___closed__2:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Async_System_instReprOSInfo_repr___redArg___closed__2_value)
        as *mut leanh::LeanObject;
pub static l_Std_Async_System_instReprOSInfo_repr___redArg___closed__3_value:
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
        core::ptr::addr_of!(l_Std_Async_System_instReprOSInfo_repr___redArg___closed__2_value)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Std_Async_System_instReprSystemUser_repr___redArg___closed__5_value)
            as *mut leanh::LeanObject,
    ],
};
static mut l_Std_Async_System_instReprOSInfo_repr___redArg___closed__3:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Async_System_instReprOSInfo_repr___redArg___closed__3_value)
        as *mut leanh::LeanObject;
static mut l_Std_Async_System_instReprOSInfo_repr___redArg___closed__4_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_Async_System_instReprOSInfo_repr___redArg___closed__4:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Std_Async_System_instReprOSInfo_repr___redArg___closed__5_value:
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
static mut l_Std_Async_System_instReprOSInfo_repr___redArg___closed__5:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Async_System_instReprOSInfo_repr___redArg___closed__5_value)
        as *mut leanh::LeanObject;
pub static l_Std_Async_System_instReprOSInfo_repr___redArg___closed__6_value:
    leanh::LeanCtorObject<1> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [
        core::ptr::addr_of!(l_Std_Async_System_instReprOSInfo_repr___redArg___closed__5_value)
            as *mut leanh::LeanObject,
    ],
};
static mut l_Std_Async_System_instReprOSInfo_repr___redArg___closed__6:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Async_System_instReprOSInfo_repr___redArg___closed__6_value)
        as *mut leanh::LeanObject;
pub static l_Std_Async_System_instReprOSInfo_repr___redArg___closed__7_value:
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
static mut l_Std_Async_System_instReprOSInfo_repr___redArg___closed__7:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Async_System_instReprOSInfo_repr___redArg___closed__7_value)
        as *mut leanh::LeanObject;
pub static l_Std_Async_System_instReprOSInfo_repr___redArg___closed__8_value:
    leanh::LeanCtorObject<1> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [
        core::ptr::addr_of!(l_Std_Async_System_instReprOSInfo_repr___redArg___closed__7_value)
            as *mut leanh::LeanObject,
    ],
};
static mut l_Std_Async_System_instReprOSInfo_repr___redArg___closed__8:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Async_System_instReprOSInfo_repr___redArg___closed__8_value)
        as *mut leanh::LeanObject;
pub static l_Std_Async_System_instReprOSInfo_repr___redArg___closed__9_value:
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
static mut l_Std_Async_System_instReprOSInfo_repr___redArg___closed__9:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Async_System_instReprOSInfo_repr___redArg___closed__9_value)
        as *mut leanh::LeanObject;
pub static l_Std_Async_System_instReprOSInfo_repr___redArg___closed__10_value:
    leanh::LeanCtorObject<1> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [
        core::ptr::addr_of!(l_Std_Async_System_instReprOSInfo_repr___redArg___closed__9_value)
            as *mut leanh::LeanObject,
    ],
};
static mut l_Std_Async_System_instReprOSInfo_repr___redArg___closed__10:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Async_System_instReprOSInfo_repr___redArg___closed__10_value)
        as *mut leanh::LeanObject;
pub static l_Std_Async_System_instReprOSInfo___closed__0_value: leanh::LeanClosureObject<0> =
    leanh::LeanClosureObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut leanh::LeanObject>() * 0)
                as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Std_Async_System_instReprOSInfo_repr___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Std_Async_System_instReprOSInfo___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Async_System_instReprOSInfo___closed__0_value)
        as *mut leanh::LeanObject;
pub static mut l_Std_Async_System_instReprOSInfo: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Async_System_instReprOSInfo___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Std_Async_System_instInhabitedOSInfo_default___closed__0_value:
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
        core::ptr::addr_of!(l_Std_Async_System_instInhabitedSystemUser_default___closed__0_value)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Std_Async_System_instInhabitedSystemUser_default___closed__0_value)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Std_Async_System_instInhabitedSystemUser_default___closed__0_value)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Std_Async_System_instInhabitedSystemUser_default___closed__0_value)
            as *mut leanh::LeanObject,
    ],
};
static mut l_Std_Async_System_instInhabitedOSInfo_default___closed__0:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Async_System_instInhabitedOSInfo_default___closed__0_value)
        as *mut leanh::LeanObject;
pub static mut l_Std_Async_System_instInhabitedOSInfo_default: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Async_System_instInhabitedOSInfo_default___closed__0_value)
        as *mut leanh::LeanObject;
pub static mut l_Std_Async_System_instInhabitedOSInfo: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Async_System_instInhabitedOSInfo_default___closed__0_value)
        as *mut leanh::LeanObject;
static mut l_Std_Async_System_instInhabitedEnvironment_default___closed__0_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_Async_System_instInhabitedEnvironment_default___closed__0:
    *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Std_Async_System_instInhabitedEnvironment_default___closed__1_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_Async_System_instInhabitedEnvironment_default___closed__1:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static mut l_Std_Async_System_instInhabitedEnvironment_default: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static mut l_Std_Async_System_instInhabitedEnvironment: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Prod_repr___at___00List_repr___at___00Std_Async_System_instReprEnvironment_repr_spec__0_spec__0___redArg___closed__0_value: leanh::LeanStringObject<2> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [40, 0]};
static mut l_Prod_repr___at___00List_repr___at___00Std_Async_System_instReprEnvironment_repr_spec__0_spec__0___redArg___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l_Prod_repr___at___00List_repr___at___00Std_Async_System_instReprEnvironment_repr_spec__0_spec__0___redArg___closed__0_value) as *mut leanh::LeanObject;
pub static l_Prod_repr___at___00List_repr___at___00Std_Async_System_instReprEnvironment_repr_spec__0_spec__0___redArg___closed__1_value: leanh::LeanStringObject<2> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [41, 0]};
static mut l_Prod_repr___at___00List_repr___at___00Std_Async_System_instReprEnvironment_repr_spec__0_spec__0___redArg___closed__1: *mut leanh::LeanObject = core::ptr::addr_of!(l_Prod_repr___at___00List_repr___at___00Std_Async_System_instReprEnvironment_repr_spec__0_spec__0___redArg___closed__1_value) as *mut leanh::LeanObject;
static mut l_Prod_repr___at___00List_repr___at___00Std_Async_System_instReprEnvironment_repr_spec__0_spec__0___redArg___closed__2_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Prod_repr___at___00List_repr___at___00Std_Async_System_instReprEnvironment_repr_spec__0_spec__0___redArg___closed__2: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Prod_repr___at___00List_repr___at___00Std_Async_System_instReprEnvironment_repr_spec__0_spec__0___redArg___closed__3_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Prod_repr___at___00List_repr___at___00Std_Async_System_instReprEnvironment_repr_spec__0_spec__0___redArg___closed__3: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Prod_repr___at___00List_repr___at___00Std_Async_System_instReprEnvironment_repr_spec__0_spec__0___redArg___closed__4_value: leanh::LeanCtorObject<1> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 3 }, m_objs: [core::ptr::addr_of!(l_Prod_repr___at___00List_repr___at___00Std_Async_System_instReprEnvironment_repr_spec__0_spec__0___redArg___closed__0_value) as *mut leanh::LeanObject] };
static mut l_Prod_repr___at___00List_repr___at___00Std_Async_System_instReprEnvironment_repr_spec__0_spec__0___redArg___closed__4: *mut leanh::LeanObject = core::ptr::addr_of!(l_Prod_repr___at___00List_repr___at___00Std_Async_System_instReprEnvironment_repr_spec__0_spec__0___redArg___closed__4_value) as *mut leanh::LeanObject;
pub static l_Prod_repr___at___00List_repr___at___00Std_Async_System_instReprEnvironment_repr_spec__0_spec__0___redArg___closed__5_value: leanh::LeanCtorObject<1> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 3 }, m_objs: [core::ptr::addr_of!(l_Prod_repr___at___00List_repr___at___00Std_Async_System_instReprEnvironment_repr_spec__0_spec__0___redArg___closed__1_value) as *mut leanh::LeanObject] };
static mut l_Prod_repr___at___00List_repr___at___00Std_Async_System_instReprEnvironment_repr_spec__0_spec__0___redArg___closed__5: *mut leanh::LeanObject = core::ptr::addr_of!(l_Prod_repr___at___00List_repr___at___00Std_Async_System_instReprEnvironment_repr_spec__0_spec__0___redArg___closed__5_value) as *mut leanh::LeanObject;
pub static l_List_repr___at___00Std_Async_System_instReprEnvironment_repr_spec__0___redArg___closed__0_value: leanh::LeanStringObject<3> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 3, m_capacity: 3, m_length: 2, m_data: [91, 93, 0]};
static mut l_List_repr___at___00Std_Async_System_instReprEnvironment_repr_spec__0___redArg___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l_List_repr___at___00Std_Async_System_instReprEnvironment_repr_spec__0___redArg___closed__0_value) as *mut leanh::LeanObject;
pub static l_List_repr___at___00Std_Async_System_instReprEnvironment_repr_spec__0___redArg___closed__1_value: leanh::LeanCtorObject<1> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 3 }, m_objs: [core::ptr::addr_of!(l_List_repr___at___00Std_Async_System_instReprEnvironment_repr_spec__0___redArg___closed__0_value) as *mut leanh::LeanObject] };
static mut l_List_repr___at___00Std_Async_System_instReprEnvironment_repr_spec__0___redArg___closed__1: *mut leanh::LeanObject = core::ptr::addr_of!(l_List_repr___at___00Std_Async_System_instReprEnvironment_repr_spec__0___redArg___closed__1_value) as *mut leanh::LeanObject;
pub static l_List_repr___at___00Std_Async_System_instReprEnvironment_repr_spec__0___redArg___closed__2_value: leanh::LeanStringObject<2> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [91, 0]};
static mut l_List_repr___at___00Std_Async_System_instReprEnvironment_repr_spec__0___redArg___closed__2: *mut leanh::LeanObject = core::ptr::addr_of!(l_List_repr___at___00Std_Async_System_instReprEnvironment_repr_spec__0___redArg___closed__2_value) as *mut leanh::LeanObject;
static mut l_List_repr___at___00Std_Async_System_instReprEnvironment_repr_spec__0___redArg___closed__3_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_List_repr___at___00Std_Async_System_instReprEnvironment_repr_spec__0___redArg___closed__3: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_List_repr___at___00Std_Async_System_instReprEnvironment_repr_spec__0___redArg___closed__4_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_List_repr___at___00Std_Async_System_instReprEnvironment_repr_spec__0___redArg___closed__4: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_List_repr___at___00Std_Async_System_instReprEnvironment_repr_spec__0___redArg___closed__5_value: leanh::LeanCtorObject<1> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 3 }, m_objs: [core::ptr::addr_of!(l_List_repr___at___00Std_Async_System_instReprEnvironment_repr_spec__0___redArg___closed__2_value) as *mut leanh::LeanObject] };
static mut l_List_repr___at___00Std_Async_System_instReprEnvironment_repr_spec__0___redArg___closed__5: *mut leanh::LeanObject = core::ptr::addr_of!(l_List_repr___at___00Std_Async_System_instReprEnvironment_repr_spec__0___redArg___closed__5_value) as *mut leanh::LeanObject;
pub static l_Std_Async_System_instReprEnvironment_repr___redArg___closed__0_value:
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
    m_data: [116, 111, 72, 97, 115, 104, 77, 97, 112, 0],
};
static mut l_Std_Async_System_instReprEnvironment_repr___redArg___closed__0:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Async_System_instReprEnvironment_repr___redArg___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Std_Async_System_instReprEnvironment_repr___redArg___closed__1_value:
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
        l_Std_Async_System_instReprEnvironment_repr___redArg___closed__0_value
    ) as *mut leanh::LeanObject],
};
static mut l_Std_Async_System_instReprEnvironment_repr___redArg___closed__1:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Async_System_instReprEnvironment_repr___redArg___closed__1_value)
        as *mut leanh::LeanObject;
pub static l_Std_Async_System_instReprEnvironment_repr___redArg___closed__2_value:
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
        core::ptr::addr_of!(l_Std_Async_System_instReprEnvironment_repr___redArg___closed__1_value)
            as *mut leanh::LeanObject,
    ],
};
static mut l_Std_Async_System_instReprEnvironment_repr___redArg___closed__2:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Async_System_instReprEnvironment_repr___redArg___closed__2_value)
        as *mut leanh::LeanObject;
pub static l_Std_Async_System_instReprEnvironment_repr___redArg___closed__3_value:
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
        core::ptr::addr_of!(l_Std_Async_System_instReprEnvironment_repr___redArg___closed__2_value)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Std_Async_System_instReprSystemUser_repr___redArg___closed__5_value)
            as *mut leanh::LeanObject,
    ],
};
static mut l_Std_Async_System_instReprEnvironment_repr___redArg___closed__3:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Async_System_instReprEnvironment_repr___redArg___closed__3_value)
        as *mut leanh::LeanObject;
pub static l_Std_Async_System_instReprEnvironment_repr___redArg___closed__4_value:
    leanh::LeanStringObject<20> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
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
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Async_System_instReprEnvironment_repr___redArg___closed__4_value)
        as *mut leanh::LeanObject;
pub static l_Std_Async_System_instReprEnvironment_repr___redArg___closed__5_value:
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
        l_Std_Async_System_instReprEnvironment_repr___redArg___closed__4_value
    ) as *mut leanh::LeanObject],
};
static mut l_Std_Async_System_instReprEnvironment_repr___redArg___closed__5:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Async_System_instReprEnvironment_repr___redArg___closed__5_value)
        as *mut leanh::LeanObject;
pub static l_Std_Async_System_instReprEnvironment___closed__0_value:
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
    m_fun: l_Std_Async_System_instReprEnvironment_repr___boxed as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Std_Async_System_instReprEnvironment___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Async_System_instReprEnvironment___closed__0_value)
        as *mut leanh::LeanObject;
pub static mut l_Std_Async_System_instReprEnvironment: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Async_System_instReprEnvironment___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Std_Async_System_Environment_get_x3f___closed__0_value:
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
    m_fun: l_String_hash___boxed as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Std_Async_System_Environment_get_x3f___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Async_System_Environment_get_x3f___closed__0_value)
        as *mut leanh::LeanObject;
static mut l_Std_Async_System_Environment_get_x3f___closed__1_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Async_System_Environment_get_x3f___closed__1: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Std_Async_System_getEnv___closed__0_value: leanh::LeanClosureObject<0> =
    leanh::LeanClosureObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut leanh::LeanObject>() * 0)
                as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Id_instMonad___lam__0 as *const core::ffi::c_void,
        m_arity: 4,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Std_Async_System_getEnv___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Async_System_getEnv___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Std_Async_System_getEnv___closed__1_value: leanh::LeanClosureObject<0> =
    leanh::LeanClosureObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut leanh::LeanObject>() * 0)
                as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Id_instMonad___lam__1___boxed as *const core::ffi::c_void,
        m_arity: 4,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Std_Async_System_getEnv___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Async_System_getEnv___closed__1_value)
        as *mut leanh::LeanObject;
pub static l_Std_Async_System_getEnv___closed__2_value: leanh::LeanClosureObject<0> =
    leanh::LeanClosureObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut leanh::LeanObject>() * 0)
                as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Id_instMonad___lam__2___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Std_Async_System_getEnv___closed__2: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Async_System_getEnv___closed__2_value)
        as *mut leanh::LeanObject;
pub static l_Std_Async_System_getEnv___closed__3_value: leanh::LeanClosureObject<0> =
    leanh::LeanClosureObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut leanh::LeanObject>() * 0)
                as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Id_instMonad___lam__3 as *const core::ffi::c_void,
        m_arity: 4,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Std_Async_System_getEnv___closed__3: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Async_System_getEnv___closed__3_value)
        as *mut leanh::LeanObject;
pub static l_Std_Async_System_getEnv___closed__4_value: leanh::LeanClosureObject<0> =
    leanh::LeanClosureObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut leanh::LeanObject>() * 0)
                as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Id_instMonad___lam__4___boxed as *const core::ffi::c_void,
        m_arity: 4,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Std_Async_System_getEnv___closed__4: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Async_System_getEnv___closed__4_value)
        as *mut leanh::LeanObject;
pub static l_Std_Async_System_getEnv___closed__5_value: leanh::LeanClosureObject<0> =
    leanh::LeanClosureObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut leanh::LeanObject>() * 0)
                as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Id_instMonad___lam__5___boxed as *const core::ffi::c_void,
        m_arity: 4,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Std_Async_System_getEnv___closed__5: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Async_System_getEnv___closed__5_value)
        as *mut leanh::LeanObject;
pub static l_Std_Async_System_getEnv___closed__6_value: leanh::LeanClosureObject<0> =
    leanh::LeanClosureObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut leanh::LeanObject>() * 0)
                as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Id_instMonad___lam__6 as *const core::ffi::c_void,
        m_arity: 4,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Std_Async_System_getEnv___closed__6: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Async_System_getEnv___closed__6_value)
        as *mut leanh::LeanObject;
pub static l_Std_Async_System_getEnv___closed__7_value: leanh::LeanCtorObject<2> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 2
                + 0) as u16,
            other: 2,
            tag: 0,
        },
        m_objs: [
            core::ptr::addr_of!(l_Std_Async_System_getEnv___closed__0_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Std_Async_System_getEnv___closed__1_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Std_Async_System_getEnv___closed__7: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Async_System_getEnv___closed__7_value)
        as *mut leanh::LeanObject;
pub static l_Std_Async_System_getEnv___closed__8_value: leanh::LeanCtorObject<5> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 5
                + 0) as u16,
            other: 5,
            tag: 0,
        },
        m_objs: [
            core::ptr::addr_of!(l_Std_Async_System_getEnv___closed__7_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Std_Async_System_getEnv___closed__2_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Std_Async_System_getEnv___closed__3_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Std_Async_System_getEnv___closed__4_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Std_Async_System_getEnv___closed__5_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Std_Async_System_getEnv___closed__8: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Async_System_getEnv___closed__8_value)
        as *mut leanh::LeanObject;
pub static l_Std_Async_System_getEnv___closed__9_value: leanh::LeanCtorObject<2> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 2
                + 0) as u16,
            other: 2,
            tag: 0,
        },
        m_objs: [
            core::ptr::addr_of!(l_Std_Async_System_getEnv___closed__8_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Std_Async_System_getEnv___closed__6_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Std_Async_System_getEnv___closed__9: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Async_System_getEnv___closed__9_value)
        as *mut leanh::LeanObject;
pub static l_Std_Async_System_getEnv___closed__10_value: leanh::LeanClosureObject<1> =
    leanh::LeanClosureObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut leanh::LeanObject>() * 1)
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
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Std_Async_System_getEnv___closed__10: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Async_System_getEnv___closed__10_value)
        as *mut leanh::LeanObject;
pub static l_Std_Async_System_getEnv___closed__11_value: leanh::LeanClosureObject<1> =
    leanh::LeanClosureObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut leanh::LeanObject>() * 1)
                as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_instForInOfForIn_x27___redArg___lam__1 as *const core::ffi::c_void,
        m_arity: 5,
        m_num_fixed: 1,
        m_objs: [
            core::ptr::addr_of!(l_Std_Async_System_getEnv___closed__10_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Std_Async_System_getEnv___closed__11: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Async_System_getEnv___closed__11_value)
        as *mut leanh::LeanObject;
pub static l_Std_Async_System_getGroup___closed__0_value: leanh::LeanClosureObject<0> =
    leanh::LeanClosureObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut leanh::LeanObject>() * 0)
                as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Std_Async_System_getGroup___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Std_Async_System_getGroup___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Async_System_getGroup___closed__0_value)
        as *mut leanh::LeanObject;
pub unsafe fn _init_l_Std_Async_System_instInhabitedGroupId_default()
-> *mut leanh::LeanObject {
    let mut v___x_1453_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1453_ = leanh::lean_unsigned_to_nat(0);
    return v___x_1453_;
}
pub unsafe fn _init_l_Std_Async_System_instInhabitedGroupId() -> *mut leanh::LeanObject {
    let mut v___x_1454_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1454_ = leanh::lean_unsigned_to_nat(0);
    return v___x_1454_;
}
pub unsafe fn l_Std_Async_System_instDecidableEqGroupId_decEq(
    mut v_x_1455_: *mut leanh::LeanObject,
    mut v_x_1456_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_1457_: u8 = 0;
    v___x_1457_ = lean_nat_dec_eq(v_x_1455_, v_x_1456_);
    return v___x_1457_;
}
pub unsafe fn l_Std_Async_System_instDecidableEqGroupId_decEq___boxed(
    mut v_x_1458_: *mut leanh::LeanObject,
    mut v_x_1459_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1460_: u8 = 0;
    let mut v_r_1461_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1460_ = l_Std_Async_System_instDecidableEqGroupId_decEq(v_x_1458_, v_x_1459_);
    leanh::lean_dec(v_x_1459_);
    leanh::lean_dec(v_x_1458_);
    v_r_1461_ = leanh::lean_box((v_res_1460_) as usize);
    return v_r_1461_;
}
pub unsafe fn l_Std_Async_System_instDecidableEqGroupId(
    mut v_x_1462_: *mut leanh::LeanObject,
    mut v_x_1463_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_1464_: u8 = 0;
    v___x_1464_ = lean_nat_dec_eq(v_x_1462_, v_x_1463_);
    return v___x_1464_;
}
pub unsafe fn l_Std_Async_System_instDecidableEqGroupId___boxed(
    mut v_x_1465_: *mut leanh::LeanObject,
    mut v_x_1466_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1467_: u8 = 0;
    let mut v_r_1468_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1467_ = l_Std_Async_System_instDecidableEqGroupId(v_x_1465_, v_x_1466_);
    leanh::lean_dec(v_x_1466_);
    leanh::lean_dec(v_x_1465_);
    v_r_1468_ = leanh::lean_box((v_res_1467_) as usize);
    return v_r_1468_;
}
pub unsafe fn l_Std_Async_System_instOrdGroupId_ord(
    mut v_x_1469_: *mut leanh::LeanObject,
    mut v_x_1470_: *mut leanh::LeanObject,
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
    mut v_x_1476_: *mut leanh::LeanObject,
    mut v_x_1477_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1478_: u8 = 0;
    let mut v_r_1479_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1478_ = l_Std_Async_System_instOrdGroupId_ord(v_x_1476_, v_x_1477_);
    leanh::lean_dec(v_x_1477_);
    leanh::lean_dec(v_x_1476_);
    v_r_1479_ = leanh::lean_box((v_res_1478_) as usize);
    return v_r_1479_;
}
pub unsafe fn l_Std_Async_System_instReprGroupId___lam__0(
    mut v_g_1485_: *mut leanh::LeanObject,
    mut v___y_1486_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1487_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1488_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1489_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1490_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1491_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1487_ = l_Std_Async_System_instReprGroupId___lam__0___closed__1;
    v___x_1488_ = l_Nat_reprFast(v_g_1485_);
    v___x_1489_ = leanh::lean_alloc_ctor(3, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_1489_, 0, v___x_1488_);
    v___x_1490_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_1490_, 0, v___x_1487_);
    leanh::lean_ctor_set(v___x_1490_, 1, v___x_1489_);
    v___x_1491_ = l_Repr_addAppParen(v___x_1490_, v___y_1486_);
    return v___x_1491_;
}
pub unsafe fn l_Std_Async_System_instReprGroupId___lam__0___boxed(
    mut v_g_1492_: *mut leanh::LeanObject,
    mut v___y_1493_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1494_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1494_ = l_Std_Async_System_instReprGroupId___lam__0(v_g_1492_, v___y_1493_);
    leanh::lean_dec(v___y_1493_);
    return v_res_1494_;
}
pub unsafe fn _init_l_Std_Async_System_instInhabitedUserId_default() -> *mut leanh::LeanObject
{
    let mut v___x_1497_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1497_ = leanh::lean_unsigned_to_nat(0);
    return v___x_1497_;
}
pub unsafe fn _init_l_Std_Async_System_instInhabitedUserId() -> *mut leanh::LeanObject {
    let mut v___x_1498_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1498_ = leanh::lean_unsigned_to_nat(0);
    return v___x_1498_;
}
pub unsafe fn l_Std_Async_System_instDecidableEqUserId_decEq(
    mut v_x_1499_: *mut leanh::LeanObject,
    mut v_x_1500_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_1501_: u8 = 0;
    v___x_1501_ = lean_nat_dec_eq(v_x_1499_, v_x_1500_);
    return v___x_1501_;
}
pub unsafe fn l_Std_Async_System_instDecidableEqUserId_decEq___boxed(
    mut v_x_1502_: *mut leanh::LeanObject,
    mut v_x_1503_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1504_: u8 = 0;
    let mut v_r_1505_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1504_ = l_Std_Async_System_instDecidableEqUserId_decEq(v_x_1502_, v_x_1503_);
    leanh::lean_dec(v_x_1503_);
    leanh::lean_dec(v_x_1502_);
    v_r_1505_ = leanh::lean_box((v_res_1504_) as usize);
    return v_r_1505_;
}
pub unsafe fn l_Std_Async_System_instDecidableEqUserId(
    mut v_x_1506_: *mut leanh::LeanObject,
    mut v_x_1507_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_1508_: u8 = 0;
    v___x_1508_ = lean_nat_dec_eq(v_x_1506_, v_x_1507_);
    return v___x_1508_;
}
pub unsafe fn l_Std_Async_System_instDecidableEqUserId___boxed(
    mut v_x_1509_: *mut leanh::LeanObject,
    mut v_x_1510_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1511_: u8 = 0;
    let mut v_r_1512_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1511_ = l_Std_Async_System_instDecidableEqUserId(v_x_1509_, v_x_1510_);
    leanh::lean_dec(v_x_1510_);
    leanh::lean_dec(v_x_1509_);
    v_r_1512_ = leanh::lean_box((v_res_1511_) as usize);
    return v_r_1512_;
}
pub unsafe fn l_Std_Async_System_instOrdUserId_ord(
    mut v_x_1513_: *mut leanh::LeanObject,
    mut v_x_1514_: *mut leanh::LeanObject,
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
    mut v_x_1520_: *mut leanh::LeanObject,
    mut v_x_1521_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1522_: u8 = 0;
    let mut v_r_1523_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1522_ = l_Std_Async_System_instOrdUserId_ord(v_x_1520_, v_x_1521_);
    leanh::lean_dec(v_x_1521_);
    leanh::lean_dec(v_x_1520_);
    v_r_1523_ = leanh::lean_box((v_res_1522_) as usize);
    return v_r_1523_;
}
pub unsafe fn l_Std_Async_System_instReprUserId___lam__0(
    mut v_u_1529_: *mut leanh::LeanObject,
    mut v___y_1530_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1531_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1532_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1533_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1534_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1535_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1531_ = l_Std_Async_System_instReprUserId___lam__0___closed__1;
    v___x_1532_ = l_Nat_reprFast(v_u_1529_);
    v___x_1533_ = leanh::lean_alloc_ctor(3, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_1533_, 0, v___x_1532_);
    v___x_1534_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_1534_, 0, v___x_1531_);
    leanh::lean_ctor_set(v___x_1534_, 1, v___x_1533_);
    v___x_1535_ = l_Repr_addAppParen(v___x_1534_, v___y_1530_);
    return v___x_1535_;
}
pub unsafe fn l_Std_Async_System_instReprUserId___lam__0___boxed(
    mut v_u_1536_: *mut leanh::LeanObject,
    mut v___y_1537_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1538_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1538_ = l_Std_Async_System_instReprUserId___lam__0(v_u_1536_, v___y_1537_);
    leanh::lean_dec(v___y_1537_);
    return v_res_1538_;
}
pub unsafe fn l_Std_Async_System_instDecidableEqSystemUser_decEq(
    mut v_x_1547_: *mut leanh::LeanObject,
    mut v_x_1548_: *mut leanh::LeanObject,
) -> u8 {
    let mut v_username_1549_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_userId_1550_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_groupId_1551_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_shell_1552_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_homeDir_1553_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_username_1554_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_userId_1555_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_groupId_1556_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_shell_1557_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_homeDir_1558_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1559_: u8 = 0;
    v_username_1549_ = leanh::lean_ctor_get(v_x_1547_, 0);
    leanh::lean_inc_ref(v_username_1549_);
    v_userId_1550_ = leanh::lean_ctor_get(v_x_1547_, 1);
    leanh::lean_inc(v_userId_1550_);
    v_groupId_1551_ = leanh::lean_ctor_get(v_x_1547_, 2);
    leanh::lean_inc(v_groupId_1551_);
    v_shell_1552_ = leanh::lean_ctor_get(v_x_1547_, 3);
    leanh::lean_inc(v_shell_1552_);
    v_homeDir_1553_ = leanh::lean_ctor_get(v_x_1547_, 4);
    leanh::lean_inc(v_homeDir_1553_);
    leanh::lean_dec_ref(v_x_1547_);
    v_username_1554_ = leanh::lean_ctor_get(v_x_1548_, 0);
    leanh::lean_inc_ref(v_username_1554_);
    v_userId_1555_ = leanh::lean_ctor_get(v_x_1548_, 1);
    leanh::lean_inc(v_userId_1555_);
    v_groupId_1556_ = leanh::lean_ctor_get(v_x_1548_, 2);
    leanh::lean_inc(v_groupId_1556_);
    v_shell_1557_ = leanh::lean_ctor_get(v_x_1548_, 3);
    leanh::lean_inc(v_shell_1557_);
    v_homeDir_1558_ = leanh::lean_ctor_get(v_x_1548_, 4);
    leanh::lean_inc(v_homeDir_1558_);
    leanh::lean_dec_ref(v_x_1548_);
    v___x_1559_ = lean_string_dec_eq(v_username_1549_, v_username_1554_);
    leanh::lean_dec_ref(v_username_1554_);
    leanh::lean_dec_ref(v_username_1549_);
    if v___x_1559_ == 0 {
        leanh::lean_dec(v_homeDir_1558_);
        leanh::lean_dec(v_shell_1557_);
        leanh::lean_dec(v_groupId_1556_);
        leanh::lean_dec(v_userId_1555_);
        leanh::lean_dec(v_homeDir_1553_);
        leanh::lean_dec(v_shell_1552_);
        leanh::lean_dec(v_groupId_1551_);
        leanh::lean_dec(v_userId_1550_);
        return v___x_1559_;
    } else {
        let mut v___x_1560_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1561_: u8 = 0;
        v___x_1560_ = leanh::lean_alloc_closure(
            l_Std_Async_System_instDecidableEqUserId___boxed as *mut core::ffi::c_void,
            2,
            0,
        );
        v___x_1561_ =
            l_Option_instDecidableEq___redArg(v___x_1560_, v_userId_1550_, v_userId_1555_);
        if v___x_1561_ == 0 {
            leanh::lean_dec(v_homeDir_1558_);
            leanh::lean_dec(v_shell_1557_);
            leanh::lean_dec(v_groupId_1556_);
            leanh::lean_dec(v_homeDir_1553_);
            leanh::lean_dec(v_shell_1552_);
            leanh::lean_dec(v_groupId_1551_);
            return v___x_1561_;
        } else {
            let mut v___x_1562_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1563_: u8 = 0;
            v___x_1562_ = leanh::lean_alloc_closure(
                l_Std_Async_System_instDecidableEqGroupId___boxed as *mut core::ffi::c_void,
                2,
                0,
            );
            v___x_1563_ =
                l_Option_instDecidableEq___redArg(v___x_1562_, v_groupId_1551_, v_groupId_1556_);
            if v___x_1563_ == 0 {
                leanh::lean_dec(v_homeDir_1558_);
                leanh::lean_dec(v_shell_1557_);
                leanh::lean_dec(v_homeDir_1553_);
                leanh::lean_dec(v_shell_1552_);
                return v___x_1563_;
            } else {
                let mut v___x_1564_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_1565_: u8 = 0;
                v___x_1564_ = leanh::lean_alloc_closure(
                    l_instDecidableEqString___boxed as *mut core::ffi::c_void,
                    2,
                    0,
                );
                v___x_1565_ =
                    l_Option_instDecidableEq___redArg(v___x_1564_, v_shell_1552_, v_shell_1557_);
                if v___x_1565_ == 0 {
                    leanh::lean_dec(v_homeDir_1558_);
                    leanh::lean_dec(v_homeDir_1553_);
                    return v___x_1565_;
                } else {
                    let mut v___x_1566_: *mut leanh::LeanObject = core::ptr::null_mut();
                    let mut v___x_1567_: u8 = 0;
                    v___x_1566_ = leanh::lean_alloc_closure(
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
    mut v_x_1568_: *mut leanh::LeanObject,
    mut v_x_1569_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1570_: u8 = 0;
    let mut v_r_1571_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1570_ = l_Std_Async_System_instDecidableEqSystemUser_decEq(v_x_1568_, v_x_1569_);
    v_r_1571_ = leanh::lean_box((v_res_1570_) as usize);
    return v_r_1571_;
}
pub unsafe fn l_Std_Async_System_instDecidableEqSystemUser(
    mut v_x_1572_: *mut leanh::LeanObject,
    mut v_x_1573_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_1574_: u8 = 0;
    v___x_1574_ = l_Std_Async_System_instDecidableEqSystemUser_decEq(v_x_1572_, v_x_1573_);
    return v___x_1574_;
}
pub unsafe fn l_Std_Async_System_instDecidableEqSystemUser___boxed(
    mut v_x_1575_: *mut leanh::LeanObject,
    mut v_x_1576_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1577_: u8 = 0;
    let mut v_r_1578_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1577_ = l_Std_Async_System_instDecidableEqSystemUser(v_x_1575_, v_x_1576_);
    v_r_1578_ = leanh::lean_box((v_res_1577_) as usize);
    return v_r_1578_;
}
pub unsafe fn l_Option_repr___at___00Std_Async_System_instReprSystemUser_repr_spec__0(
    mut v_x_1585_: *mut leanh::LeanObject,
    mut v_x_1586_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1587_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1588_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1590_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1591_: u8 = 0;
    let mut v___x_1592_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1593_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1594_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1595_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1597_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1598_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1599_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1600_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1601_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1602_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1603_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_1585_) == 0 {
                    v___x_1587_ = l_Option_repr___at___00Std_Async_System_instReprSystemUser_repr_spec__0___closed__1;
                    return v___x_1587_;
                } else {
                    v_val_1588_ = leanh::lean_ctor_get(v_x_1585_, 0);
                    v_isSharedCheck_1603_ = (!leanh::lean_is_exclusive(v_x_1585_)) as u8;
                    if v_isSharedCheck_1603_ == 0 {
                        v___x_1590_ = v_x_1585_;
                        v_isShared_1591_ = v_isSharedCheck_1603_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_val_1588_);
                        leanh::lean_dec(v_x_1585_);
                        v___x_1590_ = leanh::lean_box(0);
                        v_isShared_1591_ = v_isSharedCheck_1603_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_1592_ = l_Option_repr___at___00Std_Async_System_instReprSystemUser_repr_spec__0___closed__3;
                v___x_1593_ = leanh::lean_unsigned_to_nat(1024);
                v___x_1594_ = l_Std_Async_System_instReprUserId___lam__0___closed__1;
                v___x_1595_ = l_Nat_reprFast(v_val_1588_);
                if v_isShared_1591_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_1590_, 3);
                    leanh::lean_ctor_set(v___x_1590_, 0, v___x_1595_);
                    v___x_1597_ = v___x_1590_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1602_ = leanh::lean_alloc_ctor(3, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1602_, 0, v___x_1595_);
                    v___x_1597_ = v_reuseFailAlloc_1602_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_1598_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_1598_, 0, v___x_1594_);
                leanh::lean_ctor_set(v___x_1598_, 1, v___x_1597_);
                v___x_1599_ = l_Repr_addAppParen(v___x_1598_, v___x_1593_);
                v___x_1600_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_1600_, 0, v___x_1592_);
                leanh::lean_ctor_set(v___x_1600_, 1, v___x_1599_);
                v___x_1601_ = l_Repr_addAppParen(v___x_1600_, v_x_1586_);
                return v___x_1601_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Option_repr___at___00Std_Async_System_instReprSystemUser_repr_spec__0___boxed(
    mut v_x_1604_: *mut leanh::LeanObject,
    mut v_x_1605_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1606_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1606_ = l_Option_repr___at___00Std_Async_System_instReprSystemUser_repr_spec__0(
        v_x_1604_, v_x_1605_,
    );
    leanh::lean_dec(v_x_1605_);
    return v_res_1606_;
}
pub unsafe fn l_Option_repr___at___00Std_Async_System_instReprSystemUser_repr_spec__1(
    mut v_x_1607_: *mut leanh::LeanObject,
    mut v_x_1608_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1609_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1610_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1612_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1613_: u8 = 0;
    let mut v___x_1614_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1615_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1616_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1617_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1619_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1620_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1621_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1622_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1623_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1624_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1625_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_1607_) == 0 {
                    v___x_1609_ = l_Option_repr___at___00Std_Async_System_instReprSystemUser_repr_spec__0___closed__1;
                    return v___x_1609_;
                } else {
                    v_val_1610_ = leanh::lean_ctor_get(v_x_1607_, 0);
                    v_isSharedCheck_1625_ = (!leanh::lean_is_exclusive(v_x_1607_)) as u8;
                    if v_isSharedCheck_1625_ == 0 {
                        v___x_1612_ = v_x_1607_;
                        v_isShared_1613_ = v_isSharedCheck_1625_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_val_1610_);
                        leanh::lean_dec(v_x_1607_);
                        v___x_1612_ = leanh::lean_box(0);
                        v_isShared_1613_ = v_isSharedCheck_1625_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_1614_ = l_Option_repr___at___00Std_Async_System_instReprSystemUser_repr_spec__0___closed__3;
                v___x_1615_ = leanh::lean_unsigned_to_nat(1024);
                v___x_1616_ = l_Std_Async_System_instReprGroupId___lam__0___closed__1;
                v___x_1617_ = l_Nat_reprFast(v_val_1610_);
                if v_isShared_1613_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_1612_, 3);
                    leanh::lean_ctor_set(v___x_1612_, 0, v___x_1617_);
                    v___x_1619_ = v___x_1612_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1624_ = leanh::lean_alloc_ctor(3, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1624_, 0, v___x_1617_);
                    v___x_1619_ = v_reuseFailAlloc_1624_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_1620_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_1620_, 0, v___x_1616_);
                leanh::lean_ctor_set(v___x_1620_, 1, v___x_1619_);
                v___x_1621_ = l_Repr_addAppParen(v___x_1620_, v___x_1615_);
                v___x_1622_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_1622_, 0, v___x_1614_);
                leanh::lean_ctor_set(v___x_1622_, 1, v___x_1621_);
                v___x_1623_ = l_Repr_addAppParen(v___x_1622_, v_x_1608_);
                return v___x_1623_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Option_repr___at___00Std_Async_System_instReprSystemUser_repr_spec__1___boxed(
    mut v_x_1626_: *mut leanh::LeanObject,
    mut v_x_1627_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1628_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1628_ = l_Option_repr___at___00Std_Async_System_instReprSystemUser_repr_spec__1(
        v_x_1626_, v_x_1627_,
    );
    leanh::lean_dec(v_x_1627_);
    return v_res_1628_;
}
pub unsafe fn l_Option_repr___at___00Std_Async_System_instReprSystemUser_repr_spec__2(
    mut v_x_1629_: *mut leanh::LeanObject,
    mut v_x_1630_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1631_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1632_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1634_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1635_: u8 = 0;
    let mut v___x_1636_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1637_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1639_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1640_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1641_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1642_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1643_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_1629_) == 0 {
                    v___x_1631_ = l_Option_repr___at___00Std_Async_System_instReprSystemUser_repr_spec__0___closed__1;
                    return v___x_1631_;
                } else {
                    v_val_1632_ = leanh::lean_ctor_get(v_x_1629_, 0);
                    v_isSharedCheck_1643_ = (!leanh::lean_is_exclusive(v_x_1629_)) as u8;
                    if v_isSharedCheck_1643_ == 0 {
                        v___x_1634_ = v_x_1629_;
                        v_isShared_1635_ = v_isSharedCheck_1643_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_val_1632_);
                        leanh::lean_dec(v_x_1629_);
                        v___x_1634_ = leanh::lean_box(0);
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
                    leanh::lean_ctor_set_tag(v___x_1634_, 3);
                    leanh::lean_ctor_set(v___x_1634_, 0, v___x_1637_);
                    v___x_1639_ = v___x_1634_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1642_ = leanh::lean_alloc_ctor(3, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1642_, 0, v___x_1637_);
                    v___x_1639_ = v_reuseFailAlloc_1642_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_1640_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_1640_, 0, v___x_1636_);
                leanh::lean_ctor_set(v___x_1640_, 1, v___x_1639_);
                v___x_1641_ = l_Repr_addAppParen(v___x_1640_, v_x_1630_);
                return v___x_1641_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Option_repr___at___00Std_Async_System_instReprSystemUser_repr_spec__2___boxed(
    mut v_x_1644_: *mut leanh::LeanObject,
    mut v_x_1645_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1646_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1646_ = l_Option_repr___at___00Std_Async_System_instReprSystemUser_repr_spec__2(
        v_x_1644_, v_x_1645_,
    );
    leanh::lean_dec(v_x_1645_);
    return v_res_1646_;
}
pub unsafe fn l_Option_repr___at___00Std_Async_System_instReprSystemUser_repr_spec__3(
    mut v_x_1650_: *mut leanh::LeanObject,
    mut v_x_1651_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1652_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1653_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1655_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1656_: u8 = 0;
    let mut v___x_1657_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1658_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1659_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1660_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1662_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1663_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1664_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1665_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1666_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1667_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1668_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_1650_) == 0 {
                    v___x_1652_ = l_Option_repr___at___00Std_Async_System_instReprSystemUser_repr_spec__0___closed__1;
                    return v___x_1652_;
                } else {
                    v_val_1653_ = leanh::lean_ctor_get(v_x_1650_, 0);
                    v_isSharedCheck_1668_ = (!leanh::lean_is_exclusive(v_x_1650_)) as u8;
                    if v_isSharedCheck_1668_ == 0 {
                        v___x_1655_ = v_x_1650_;
                        v_isShared_1656_ = v_isSharedCheck_1668_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_val_1653_);
                        leanh::lean_dec(v_x_1650_);
                        v___x_1655_ = leanh::lean_box(0);
                        v_isShared_1656_ = v_isSharedCheck_1668_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_1657_ = l_Option_repr___at___00Std_Async_System_instReprSystemUser_repr_spec__0___closed__3;
                v___x_1658_ = leanh::lean_unsigned_to_nat(1024);
                v___x_1659_ = l_Option_repr___at___00Std_Async_System_instReprSystemUser_repr_spec__3___closed__1;
                v___x_1660_ = l_String_quote(v_val_1653_);
                if v_isShared_1656_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_1655_, 3);
                    leanh::lean_ctor_set(v___x_1655_, 0, v___x_1660_);
                    v___x_1662_ = v___x_1655_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1667_ = leanh::lean_alloc_ctor(3, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1667_, 0, v___x_1660_);
                    v___x_1662_ = v_reuseFailAlloc_1667_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_1663_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_1663_, 0, v___x_1659_);
                leanh::lean_ctor_set(v___x_1663_, 1, v___x_1662_);
                v___x_1664_ = l_Repr_addAppParen(v___x_1663_, v___x_1658_);
                v___x_1665_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_1665_, 0, v___x_1657_);
                leanh::lean_ctor_set(v___x_1665_, 1, v___x_1664_);
                v___x_1666_ = l_Repr_addAppParen(v___x_1665_, v_x_1651_);
                return v___x_1666_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Option_repr___at___00Std_Async_System_instReprSystemUser_repr_spec__3___boxed(
    mut v_x_1669_: *mut leanh::LeanObject,
    mut v_x_1670_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1671_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1671_ = l_Option_repr___at___00Std_Async_System_instReprSystemUser_repr_spec__3(
        v_x_1669_, v_x_1670_,
    );
    leanh::lean_dec(v_x_1670_);
    return v_res_1671_;
}
pub unsafe fn l_Nat_cast___at___00Std_Async_System_instReprSystemUser_repr_spec__4(
    mut v_a_1672_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1673_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1673_ = lean_nat_to_int(v_a_1672_);
    return v___x_1673_;
}
pub unsafe fn _init_l_Std_Async_System_instReprSystemUser_repr___redArg___closed__7()
-> *mut leanh::LeanObject {
    let mut v___x_1687_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1688_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1687_ = leanh::lean_unsigned_to_nat(12);
    v___x_1688_ = lean_nat_to_int(v___x_1687_);
    return v___x_1688_;
}
pub unsafe fn _init_l_Std_Async_System_instReprSystemUser_repr___redArg___closed__12()
-> *mut leanh::LeanObject {
    let mut v___x_1695_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1696_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1695_ = leanh::lean_unsigned_to_nat(10);
    v___x_1696_ = lean_nat_to_int(v___x_1695_);
    return v___x_1696_;
}
pub unsafe fn _init_l_Std_Async_System_instReprSystemUser_repr___redArg___closed__15()
-> *mut leanh::LeanObject {
    let mut v___x_1700_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1701_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1700_ = leanh::lean_unsigned_to_nat(11);
    v___x_1701_ = lean_nat_to_int(v___x_1700_);
    return v___x_1701_;
}
pub unsafe fn _init_l_Std_Async_System_instReprSystemUser_repr___redArg___closed__18()
-> *mut leanh::LeanObject {
    let mut v___x_1705_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1706_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1705_ = leanh::lean_unsigned_to_nat(9);
    v___x_1706_ = lean_nat_to_int(v___x_1705_);
    return v___x_1706_;
}
pub unsafe fn _init_l_Std_Async_System_instReprSystemUser_repr___redArg___closed__22()
-> *mut leanh::LeanObject {
    let mut v___x_1711_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1712_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1711_ = l_Std_Async_System_instReprSystemUser_repr___redArg___closed__0;
    v___x_1712_ = lean_string_length(v___x_1711_);
    return v___x_1712_;
}
pub unsafe fn _init_l_Std_Async_System_instReprSystemUser_repr___redArg___closed__23()
-> *mut leanh::LeanObject {
    let mut v___x_1713_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1714_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1713_ = leanh::lean_obj_once(
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
    mut v_x_1719_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_username_1720_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_userId_1721_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_groupId_1722_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_shell_1723_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_homeDir_1724_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1725_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1726_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1727_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1728_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1729_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1730_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1731_: u8 = 0;
    let mut v___x_1732_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1733_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1734_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1735_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1736_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1737_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1738_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1739_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1740_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1741_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1742_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1743_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1744_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1745_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1746_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1747_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1748_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1749_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1750_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1751_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1752_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1753_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1754_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1755_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1756_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1757_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1758_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1759_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1760_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1761_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1762_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1763_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1764_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1765_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1766_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1767_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1768_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1769_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1770_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1771_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1772_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1773_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1774_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1775_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1776_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1777_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1778_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1779_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1780_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1781_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1782_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_username_1720_ = leanh::lean_ctor_get(v_x_1719_, 0);
    leanh::lean_inc_ref(v_username_1720_);
    v_userId_1721_ = leanh::lean_ctor_get(v_x_1719_, 1);
    leanh::lean_inc(v_userId_1721_);
    v_groupId_1722_ = leanh::lean_ctor_get(v_x_1719_, 2);
    leanh::lean_inc(v_groupId_1722_);
    v_shell_1723_ = leanh::lean_ctor_get(v_x_1719_, 3);
    leanh::lean_inc(v_shell_1723_);
    v_homeDir_1724_ = leanh::lean_ctor_get(v_x_1719_, 4);
    leanh::lean_inc(v_homeDir_1724_);
    leanh::lean_dec_ref(v_x_1719_);
    v___x_1725_ = l_Std_Async_System_instReprSystemUser_repr___redArg___closed__5;
    v___x_1726_ = l_Std_Async_System_instReprSystemUser_repr___redArg___closed__6;
    v___x_1727_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Async_System_instReprSystemUser_repr___redArg___closed__7),
        core::ptr::addr_of_mut!(
            l_Std_Async_System_instReprSystemUser_repr___redArg___closed__7_once
        ),
        _init_l_Std_Async_System_instReprSystemUser_repr___redArg___closed__7,
    );
    v___x_1728_ = l_String_quote(v_username_1720_);
    v___x_1729_ = leanh::lean_alloc_ctor(3, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_1729_, 0, v___x_1728_);
    v___x_1730_ = leanh::lean_alloc_ctor(4, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_1730_, 0, v___x_1727_);
    leanh::lean_ctor_set(v___x_1730_, 1, v___x_1729_);
    v___x_1731_ = 0;
    v___x_1732_ = leanh::lean_alloc_ctor(6, 1, (1) as u32);
    leanh::lean_ctor_set(v___x_1732_, 0, v___x_1730_);
    leanh::lean_ctor_set_uint8(
        v___x_1732_,
        (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
        v___x_1731_,
    );
    v___x_1733_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_1733_, 0, v___x_1726_);
    leanh::lean_ctor_set(v___x_1733_, 1, v___x_1732_);
    v___x_1734_ = l_Std_Async_System_instReprSystemUser_repr___redArg___closed__9;
    v___x_1735_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_1735_, 0, v___x_1733_);
    leanh::lean_ctor_set(v___x_1735_, 1, v___x_1734_);
    v___x_1736_ = leanh::lean_box(1);
    v___x_1737_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_1737_, 0, v___x_1735_);
    leanh::lean_ctor_set(v___x_1737_, 1, v___x_1736_);
    v___x_1738_ = l_Std_Async_System_instReprSystemUser_repr___redArg___closed__11;
    v___x_1739_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_1739_, 0, v___x_1737_);
    leanh::lean_ctor_set(v___x_1739_, 1, v___x_1738_);
    v___x_1740_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_1740_, 0, v___x_1739_);
    leanh::lean_ctor_set(v___x_1740_, 1, v___x_1725_);
    v___x_1741_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Async_System_instReprSystemUser_repr___redArg___closed__12),
        core::ptr::addr_of_mut!(
            l_Std_Async_System_instReprSystemUser_repr___redArg___closed__12_once
        ),
        _init_l_Std_Async_System_instReprSystemUser_repr___redArg___closed__12,
    );
    v___x_1742_ = leanh::lean_unsigned_to_nat(0);
    v___x_1743_ = l_Option_repr___at___00Std_Async_System_instReprSystemUser_repr_spec__0(
        v_userId_1721_,
        v___x_1742_,
    );
    v___x_1744_ = leanh::lean_alloc_ctor(4, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_1744_, 0, v___x_1741_);
    leanh::lean_ctor_set(v___x_1744_, 1, v___x_1743_);
    v___x_1745_ = leanh::lean_alloc_ctor(6, 1, (1) as u32);
    leanh::lean_ctor_set(v___x_1745_, 0, v___x_1744_);
    leanh::lean_ctor_set_uint8(
        v___x_1745_,
        (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
        v___x_1731_,
    );
    v___x_1746_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_1746_, 0, v___x_1740_);
    leanh::lean_ctor_set(v___x_1746_, 1, v___x_1745_);
    v___x_1747_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_1747_, 0, v___x_1746_);
    leanh::lean_ctor_set(v___x_1747_, 1, v___x_1734_);
    v___x_1748_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_1748_, 0, v___x_1747_);
    leanh::lean_ctor_set(v___x_1748_, 1, v___x_1736_);
    v___x_1749_ = l_Std_Async_System_instReprSystemUser_repr___redArg___closed__14;
    v___x_1750_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_1750_, 0, v___x_1748_);
    leanh::lean_ctor_set(v___x_1750_, 1, v___x_1749_);
    v___x_1751_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_1751_, 0, v___x_1750_);
    leanh::lean_ctor_set(v___x_1751_, 1, v___x_1725_);
    v___x_1752_ = leanh::lean_obj_once(
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
    v___x_1754_ = leanh::lean_alloc_ctor(4, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_1754_, 0, v___x_1752_);
    leanh::lean_ctor_set(v___x_1754_, 1, v___x_1753_);
    v___x_1755_ = leanh::lean_alloc_ctor(6, 1, (1) as u32);
    leanh::lean_ctor_set(v___x_1755_, 0, v___x_1754_);
    leanh::lean_ctor_set_uint8(
        v___x_1755_,
        (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
        v___x_1731_,
    );
    v___x_1756_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_1756_, 0, v___x_1751_);
    leanh::lean_ctor_set(v___x_1756_, 1, v___x_1755_);
    v___x_1757_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_1757_, 0, v___x_1756_);
    leanh::lean_ctor_set(v___x_1757_, 1, v___x_1734_);
    v___x_1758_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_1758_, 0, v___x_1757_);
    leanh::lean_ctor_set(v___x_1758_, 1, v___x_1736_);
    v___x_1759_ = l_Std_Async_System_instReprSystemUser_repr___redArg___closed__17;
    v___x_1760_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_1760_, 0, v___x_1758_);
    leanh::lean_ctor_set(v___x_1760_, 1, v___x_1759_);
    v___x_1761_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_1761_, 0, v___x_1760_);
    leanh::lean_ctor_set(v___x_1761_, 1, v___x_1725_);
    v___x_1762_ = leanh::lean_obj_once(
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
    v___x_1764_ = leanh::lean_alloc_ctor(4, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_1764_, 0, v___x_1762_);
    leanh::lean_ctor_set(v___x_1764_, 1, v___x_1763_);
    v___x_1765_ = leanh::lean_alloc_ctor(6, 1, (1) as u32);
    leanh::lean_ctor_set(v___x_1765_, 0, v___x_1764_);
    leanh::lean_ctor_set_uint8(
        v___x_1765_,
        (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
        v___x_1731_,
    );
    v___x_1766_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_1766_, 0, v___x_1761_);
    leanh::lean_ctor_set(v___x_1766_, 1, v___x_1765_);
    v___x_1767_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_1767_, 0, v___x_1766_);
    leanh::lean_ctor_set(v___x_1767_, 1, v___x_1734_);
    v___x_1768_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_1768_, 0, v___x_1767_);
    leanh::lean_ctor_set(v___x_1768_, 1, v___x_1736_);
    v___x_1769_ = l_Std_Async_System_instReprSystemUser_repr___redArg___closed__20;
    v___x_1770_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_1770_, 0, v___x_1768_);
    leanh::lean_ctor_set(v___x_1770_, 1, v___x_1769_);
    v___x_1771_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_1771_, 0, v___x_1770_);
    leanh::lean_ctor_set(v___x_1771_, 1, v___x_1725_);
    v___x_1772_ = l_Option_repr___at___00Std_Async_System_instReprSystemUser_repr_spec__3(
        v_homeDir_1724_,
        v___x_1742_,
    );
    v___x_1773_ = leanh::lean_alloc_ctor(4, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_1773_, 0, v___x_1752_);
    leanh::lean_ctor_set(v___x_1773_, 1, v___x_1772_);
    v___x_1774_ = leanh::lean_alloc_ctor(6, 1, (1) as u32);
    leanh::lean_ctor_set(v___x_1774_, 0, v___x_1773_);
    leanh::lean_ctor_set_uint8(
        v___x_1774_,
        (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
        v___x_1731_,
    );
    v___x_1775_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_1775_, 0, v___x_1771_);
    leanh::lean_ctor_set(v___x_1775_, 1, v___x_1774_);
    v___x_1776_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Async_System_instReprSystemUser_repr___redArg___closed__23),
        core::ptr::addr_of_mut!(
            l_Std_Async_System_instReprSystemUser_repr___redArg___closed__23_once
        ),
        _init_l_Std_Async_System_instReprSystemUser_repr___redArg___closed__23,
    );
    v___x_1777_ = l_Std_Async_System_instReprSystemUser_repr___redArg___closed__24;
    v___x_1778_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_1778_, 0, v___x_1777_);
    leanh::lean_ctor_set(v___x_1778_, 1, v___x_1775_);
    v___x_1779_ = l_Std_Async_System_instReprSystemUser_repr___redArg___closed__25;
    v___x_1780_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_1780_, 0, v___x_1778_);
    leanh::lean_ctor_set(v___x_1780_, 1, v___x_1779_);
    v___x_1781_ = leanh::lean_alloc_ctor(4, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_1781_, 0, v___x_1776_);
    leanh::lean_ctor_set(v___x_1781_, 1, v___x_1780_);
    v___x_1782_ = leanh::lean_alloc_ctor(6, 1, (1) as u32);
    leanh::lean_ctor_set(v___x_1782_, 0, v___x_1781_);
    leanh::lean_ctor_set_uint8(
        v___x_1782_,
        (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
        v___x_1731_,
    );
    return v___x_1782_;
}
pub unsafe fn l_Std_Async_System_instReprSystemUser_repr(
    mut v_x_1783_: *mut leanh::LeanObject,
    mut v_prec_1784_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1785_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1785_ = l_Std_Async_System_instReprSystemUser_repr___redArg(v_x_1783_);
    return v___x_1785_;
}
pub unsafe fn l_Std_Async_System_instReprSystemUser_repr___boxed(
    mut v_x_1786_: *mut leanh::LeanObject,
    mut v_prec_1787_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1788_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1788_ = l_Std_Async_System_instReprSystemUser_repr(v_x_1786_, v_prec_1787_);
    leanh::lean_dec(v_prec_1787_);
    return v_res_1788_;
}
pub unsafe fn l_Std_Format_joinSep___at___00Array_repr___at___00Std_Async_System_instReprGroupInfo_repr_spec__0_spec__0___lam__0(
    mut v___y_1791_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1792_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1793_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1792_ = l_String_quote(v___y_1791_);
    v___x_1793_ = leanh::lean_alloc_ctor(3, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_1793_, 0, v___x_1792_);
    return v___x_1793_;
}
pub unsafe fn l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Std_Async_System_instReprGroupInfo_repr_spec__0_spec__0_spec__1_spec__2(
    mut v_x_1794_: *mut leanh::LeanObject,
    mut v_x_1795_: *mut leanh::LeanObject,
    mut v_x_1796_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_head_1797_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_1798_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1800_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1801_: u8 = 0;
    let mut v___x_1803_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1804_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1805_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1806_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1808_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1809_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_1796_) == 0 {
                    leanh::lean_dec(v_x_1794_);
                    return v_x_1795_;
                } else {
                    v_head_1797_ = leanh::lean_ctor_get(v_x_1796_, 0);
                    v_tail_1798_ = leanh::lean_ctor_get(v_x_1796_, 1);
                    v_isSharedCheck_1809_ = (!leanh::lean_is_exclusive(v_x_1796_)) as u8;
                    if v_isSharedCheck_1809_ == 0 {
                        v___x_1800_ = v_x_1796_;
                        v_isShared_1801_ = v_isSharedCheck_1809_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_tail_1798_);
                        leanh::lean_inc(v_head_1797_);
                        leanh::lean_dec(v_x_1796_);
                        v___x_1800_ = leanh::lean_box(0);
                        v_isShared_1801_ = v_isSharedCheck_1809_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                leanh::lean_inc(v_x_1794_);
                if v_isShared_1801_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_1800_, 5);
                    leanh::lean_ctor_set(v___x_1800_, 1, v_x_1794_);
                    leanh::lean_ctor_set(v___x_1800_, 0, v_x_1795_);
                    v___x_1803_ = v___x_1800_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1808_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1808_, 0, v_x_1795_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1808_, 1, v_x_1794_);
                    v___x_1803_ = v_reuseFailAlloc_1808_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_1804_ = l_String_quote(v_head_1797_);
                v___x_1805_ = leanh::lean_alloc_ctor(3, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_1805_, 0, v___x_1804_);
                v___x_1806_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_1806_, 0, v___x_1803_);
                leanh::lean_ctor_set(v___x_1806_, 1, v___x_1805_);
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
    mut v_x_1810_: *mut leanh::LeanObject,
    mut v_x_1811_: *mut leanh::LeanObject,
    mut v_x_1812_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_head_1813_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_1814_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1816_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1817_: u8 = 0;
    let mut v___x_1819_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1820_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1821_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1822_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1823_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1824_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1825_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_1812_) == 0 {
                    leanh::lean_dec(v_x_1810_);
                    return v_x_1811_;
                } else {
                    v_head_1813_ = leanh::lean_ctor_get(v_x_1812_, 0);
                    v_tail_1814_ = leanh::lean_ctor_get(v_x_1812_, 1);
                    v_isSharedCheck_1825_ = (!leanh::lean_is_exclusive(v_x_1812_)) as u8;
                    if v_isSharedCheck_1825_ == 0 {
                        v___x_1816_ = v_x_1812_;
                        v_isShared_1817_ = v_isSharedCheck_1825_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_tail_1814_);
                        leanh::lean_inc(v_head_1813_);
                        leanh::lean_dec(v_x_1812_);
                        v___x_1816_ = leanh::lean_box(0);
                        v_isShared_1817_ = v_isSharedCheck_1825_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                leanh::lean_inc(v_x_1810_);
                if v_isShared_1817_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_1816_, 5);
                    leanh::lean_ctor_set(v___x_1816_, 1, v_x_1810_);
                    leanh::lean_ctor_set(v___x_1816_, 0, v_x_1811_);
                    v___x_1819_ = v___x_1816_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1824_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1824_, 0, v_x_1811_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1824_, 1, v_x_1810_);
                    v___x_1819_ = v_reuseFailAlloc_1824_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_1820_ = l_String_quote(v_head_1813_);
                v___x_1821_ = leanh::lean_alloc_ctor(3, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_1821_, 0, v___x_1820_);
                v___x_1822_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_1822_, 0, v___x_1819_);
                leanh::lean_ctor_set(v___x_1822_, 1, v___x_1821_);
                v___x_1823_ = l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Std_Async_System_instReprGroupInfo_repr_spec__0_spec__0_spec__1_spec__2(v_x_1810_, v___x_1822_, v_tail_1814_);
                return v___x_1823_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Format_joinSep___at___00Array_repr___at___00Std_Async_System_instReprGroupInfo_repr_spec__0_spec__0(
    mut v_x_1826_: *mut leanh::LeanObject,
    mut v_x_1827_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_x_1826_) == 0 {
        let mut v___x_1828_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_x_1827_);
        v___x_1828_ = leanh::lean_box(0);
        return v___x_1828_;
    } else {
        let mut v_tail_1829_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_tail_1829_ = leanh::lean_ctor_get(v_x_1826_, 1);
        if leanh::lean_obj_tag(v_tail_1829_) == 0 {
            let mut v_head_1830_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1831_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_x_1827_);
            v_head_1830_ = leanh::lean_ctor_get(v_x_1826_, 0);
            leanh::lean_inc(v_head_1830_);
            leanh::lean_dec_ref_known(v_x_1826_, 2);
            v___x_1831_ = l_Std_Format_joinSep___at___00Array_repr___at___00Std_Async_System_instReprGroupInfo_repr_spec__0_spec__0___lam__0(v_head_1830_);
            return v___x_1831_;
        } else {
            let mut v_head_1832_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1833_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1834_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_inc(v_tail_1829_);
            v_head_1832_ = leanh::lean_ctor_get(v_x_1826_, 0);
            leanh::lean_inc(v_head_1832_);
            leanh::lean_dec_ref_known(v_x_1826_, 2);
            v___x_1833_ = l_Std_Format_joinSep___at___00Array_repr___at___00Std_Async_System_instReprGroupInfo_repr_spec__0_spec__0___lam__0(v_head_1832_);
            v___x_1834_ = l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Std_Async_System_instReprGroupInfo_repr_spec__0_spec__0_spec__1(v_x_1827_, v___x_1833_, v_tail_1829_);
            return v___x_1834_;
        }
    }
}
pub unsafe fn _init_l_Array_repr___at___00Std_Async_System_instReprGroupInfo_repr_spec__0___closed__3()
-> *mut leanh::LeanObject {
    let mut v___x_1840_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1841_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1840_ = l_Array_repr___at___00Std_Async_System_instReprGroupInfo_repr_spec__0___closed__0;
    v___x_1841_ = lean_string_length(v___x_1840_);
    return v___x_1841_;
}
pub unsafe fn _init_l_Array_repr___at___00Std_Async_System_instReprGroupInfo_repr_spec__0___closed__4()
-> *mut leanh::LeanObject {
    let mut v___x_1842_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1843_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1842_ = leanh::lean_obj_once(
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
    mut v_xs_1851_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1852_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1853_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1854_: u8 = 0;
    v___x_1852_ = lean_array_get_size(v_xs_1851_);
    v___x_1853_ = leanh::lean_unsigned_to_nat(0);
    v___x_1854_ = lean_nat_dec_eq(v___x_1852_, v___x_1853_);
    if v___x_1854_ == 0 {
        let mut v___x_1855_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1856_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1857_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1858_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1859_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1860_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1861_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1862_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1863_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1864_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_1855_ = lean_array_to_list(v_xs_1851_);
        v___x_1856_ =
            l_Array_repr___at___00Std_Async_System_instReprGroupInfo_repr_spec__0___closed__1;
        v___x_1857_ = l_Std_Format_joinSep___at___00Array_repr___at___00Std_Async_System_instReprGroupInfo_repr_spec__0_spec__0(v___x_1855_, v___x_1856_);
        v___x_1858_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Array_repr___at___00Std_Async_System_instReprGroupInfo_repr_spec__0___closed__4), core::ptr::addr_of_mut!(l_Array_repr___at___00Std_Async_System_instReprGroupInfo_repr_spec__0___closed__4_once), _init_l_Array_repr___at___00Std_Async_System_instReprGroupInfo_repr_spec__0___closed__4);
        v___x_1859_ =
            l_Array_repr___at___00Std_Async_System_instReprGroupInfo_repr_spec__0___closed__5;
        v___x_1860_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
        leanh::lean_ctor_set(v___x_1860_, 0, v___x_1859_);
        leanh::lean_ctor_set(v___x_1860_, 1, v___x_1857_);
        v___x_1861_ =
            l_Array_repr___at___00Std_Async_System_instReprGroupInfo_repr_spec__0___closed__6;
        v___x_1862_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
        leanh::lean_ctor_set(v___x_1862_, 0, v___x_1860_);
        leanh::lean_ctor_set(v___x_1862_, 1, v___x_1861_);
        v___x_1863_ = leanh::lean_alloc_ctor(4, 2, (0) as u32);
        leanh::lean_ctor_set(v___x_1863_, 0, v___x_1858_);
        leanh::lean_ctor_set(v___x_1863_, 1, v___x_1862_);
        v___x_1864_ = l_Std_Format_fill(v___x_1863_);
        return v___x_1864_;
    } else {
        let mut v___x_1865_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec_ref(v_xs_1851_);
        v___x_1865_ =
            l_Array_repr___at___00Std_Async_System_instReprGroupInfo_repr_spec__0___closed__8;
        return v___x_1865_;
    }
}
pub unsafe fn _init_l_Std_Async_System_instReprGroupInfo_repr___redArg___closed__4()
-> *mut leanh::LeanObject {
    let mut v___x_1875_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1876_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1875_ = leanh::lean_unsigned_to_nat(13);
    v___x_1876_ = lean_nat_to_int(v___x_1875_);
    return v___x_1876_;
}
pub unsafe fn l_Std_Async_System_instReprGroupInfo_repr___redArg(
    mut v_x_1880_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_groupName_1881_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_groupId_1882_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_members_1883_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1884_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1885_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1886_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1887_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1888_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1889_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1890_: u8 = 0;
    let mut v___x_1891_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1892_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1893_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1894_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1895_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1896_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1897_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1898_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1899_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1900_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1901_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1902_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1903_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1904_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1905_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1906_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1907_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1908_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1909_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1910_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1911_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1912_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1913_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1914_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1915_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1916_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1917_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1918_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1919_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1920_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1921_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1922_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1923_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1924_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1925_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_groupName_1881_ = leanh::lean_ctor_get(v_x_1880_, 0);
    leanh::lean_inc_ref(v_groupName_1881_);
    v_groupId_1882_ = leanh::lean_ctor_get(v_x_1880_, 1);
    leanh::lean_inc(v_groupId_1882_);
    v_members_1883_ = leanh::lean_ctor_get(v_x_1880_, 2);
    leanh::lean_inc_ref(v_members_1883_);
    leanh::lean_dec_ref(v_x_1880_);
    v___x_1884_ = l_Std_Async_System_instReprSystemUser_repr___redArg___closed__5;
    v___x_1885_ = l_Std_Async_System_instReprGroupInfo_repr___redArg___closed__3;
    v___x_1886_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Async_System_instReprGroupInfo_repr___redArg___closed__4),
        core::ptr::addr_of_mut!(
            l_Std_Async_System_instReprGroupInfo_repr___redArg___closed__4_once
        ),
        _init_l_Std_Async_System_instReprGroupInfo_repr___redArg___closed__4,
    );
    v___x_1887_ = l_String_quote(v_groupName_1881_);
    v___x_1888_ = leanh::lean_alloc_ctor(3, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_1888_, 0, v___x_1887_);
    v___x_1889_ = leanh::lean_alloc_ctor(4, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_1889_, 0, v___x_1886_);
    leanh::lean_ctor_set(v___x_1889_, 1, v___x_1888_);
    v___x_1890_ = 0;
    v___x_1891_ = leanh::lean_alloc_ctor(6, 1, (1) as u32);
    leanh::lean_ctor_set(v___x_1891_, 0, v___x_1889_);
    leanh::lean_ctor_set_uint8(
        v___x_1891_,
        (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
        v___x_1890_,
    );
    v___x_1892_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_1892_, 0, v___x_1885_);
    leanh::lean_ctor_set(v___x_1892_, 1, v___x_1891_);
    v___x_1893_ = l_Std_Async_System_instReprSystemUser_repr___redArg___closed__9;
    v___x_1894_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_1894_, 0, v___x_1892_);
    leanh::lean_ctor_set(v___x_1894_, 1, v___x_1893_);
    v___x_1895_ = leanh::lean_box(1);
    v___x_1896_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_1896_, 0, v___x_1894_);
    leanh::lean_ctor_set(v___x_1896_, 1, v___x_1895_);
    v___x_1897_ = l_Std_Async_System_instReprSystemUser_repr___redArg___closed__14;
    v___x_1898_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_1898_, 0, v___x_1896_);
    leanh::lean_ctor_set(v___x_1898_, 1, v___x_1897_);
    v___x_1899_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_1899_, 0, v___x_1898_);
    leanh::lean_ctor_set(v___x_1899_, 1, v___x_1884_);
    v___x_1900_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Async_System_instReprSystemUser_repr___redArg___closed__15),
        core::ptr::addr_of_mut!(
            l_Std_Async_System_instReprSystemUser_repr___redArg___closed__15_once
        ),
        _init_l_Std_Async_System_instReprSystemUser_repr___redArg___closed__15,
    );
    v___x_1901_ = leanh::lean_unsigned_to_nat(0);
    v___x_1902_ = l_Std_Async_System_instReprGroupId___lam__0___closed__1;
    v___x_1903_ = l_Nat_reprFast(v_groupId_1882_);
    v___x_1904_ = leanh::lean_alloc_ctor(3, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_1904_, 0, v___x_1903_);
    v___x_1905_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_1905_, 0, v___x_1902_);
    leanh::lean_ctor_set(v___x_1905_, 1, v___x_1904_);
    v___x_1906_ = l_Repr_addAppParen(v___x_1905_, v___x_1901_);
    v___x_1907_ = leanh::lean_alloc_ctor(4, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_1907_, 0, v___x_1900_);
    leanh::lean_ctor_set(v___x_1907_, 1, v___x_1906_);
    v___x_1908_ = leanh::lean_alloc_ctor(6, 1, (1) as u32);
    leanh::lean_ctor_set(v___x_1908_, 0, v___x_1907_);
    leanh::lean_ctor_set_uint8(
        v___x_1908_,
        (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
        v___x_1890_,
    );
    v___x_1909_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_1909_, 0, v___x_1899_);
    leanh::lean_ctor_set(v___x_1909_, 1, v___x_1908_);
    v___x_1910_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_1910_, 0, v___x_1909_);
    leanh::lean_ctor_set(v___x_1910_, 1, v___x_1893_);
    v___x_1911_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_1911_, 0, v___x_1910_);
    leanh::lean_ctor_set(v___x_1911_, 1, v___x_1895_);
    v___x_1912_ = l_Std_Async_System_instReprGroupInfo_repr___redArg___closed__6;
    v___x_1913_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_1913_, 0, v___x_1911_);
    leanh::lean_ctor_set(v___x_1913_, 1, v___x_1912_);
    v___x_1914_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_1914_, 0, v___x_1913_);
    leanh::lean_ctor_set(v___x_1914_, 1, v___x_1884_);
    v___x_1915_ =
        l_Array_repr___at___00Std_Async_System_instReprGroupInfo_repr_spec__0(v_members_1883_);
    v___x_1916_ = leanh::lean_alloc_ctor(4, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_1916_, 0, v___x_1900_);
    leanh::lean_ctor_set(v___x_1916_, 1, v___x_1915_);
    v___x_1917_ = leanh::lean_alloc_ctor(6, 1, (1) as u32);
    leanh::lean_ctor_set(v___x_1917_, 0, v___x_1916_);
    leanh::lean_ctor_set_uint8(
        v___x_1917_,
        (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
        v___x_1890_,
    );
    v___x_1918_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_1918_, 0, v___x_1914_);
    leanh::lean_ctor_set(v___x_1918_, 1, v___x_1917_);
    v___x_1919_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Async_System_instReprSystemUser_repr___redArg___closed__23),
        core::ptr::addr_of_mut!(
            l_Std_Async_System_instReprSystemUser_repr___redArg___closed__23_once
        ),
        _init_l_Std_Async_System_instReprSystemUser_repr___redArg___closed__23,
    );
    v___x_1920_ = l_Std_Async_System_instReprSystemUser_repr___redArg___closed__24;
    v___x_1921_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_1921_, 0, v___x_1920_);
    leanh::lean_ctor_set(v___x_1921_, 1, v___x_1918_);
    v___x_1922_ = l_Std_Async_System_instReprSystemUser_repr___redArg___closed__25;
    v___x_1923_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_1923_, 0, v___x_1921_);
    leanh::lean_ctor_set(v___x_1923_, 1, v___x_1922_);
    v___x_1924_ = leanh::lean_alloc_ctor(4, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_1924_, 0, v___x_1919_);
    leanh::lean_ctor_set(v___x_1924_, 1, v___x_1923_);
    v___x_1925_ = leanh::lean_alloc_ctor(6, 1, (1) as u32);
    leanh::lean_ctor_set(v___x_1925_, 0, v___x_1924_);
    leanh::lean_ctor_set_uint8(
        v___x_1925_,
        (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
        v___x_1890_,
    );
    return v___x_1925_;
}
pub unsafe fn l_Std_Async_System_instReprGroupInfo_repr(
    mut v_x_1926_: *mut leanh::LeanObject,
    mut v_prec_1927_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1928_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1928_ = l_Std_Async_System_instReprGroupInfo_repr___redArg(v_x_1926_);
    return v___x_1928_;
}
pub unsafe fn l_Std_Async_System_instReprGroupInfo_repr___boxed(
    mut v_x_1929_: *mut leanh::LeanObject,
    mut v_prec_1930_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1931_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1931_ = l_Std_Async_System_instReprGroupInfo_repr(v_x_1929_, v_prec_1930_);
    leanh::lean_dec(v_prec_1930_);
    return v_res_1931_;
}
pub unsafe fn _init_l_Std_Async_System_instInhabitedCPUTimes_default___closed__0()
-> *mut leanh::LeanObject {
    let mut v___x_1942_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1943_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1942_ = l_Std_Time_Millisecond_instInhabitedOffset;
    v___x_1943_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
    leanh::lean_ctor_set(v___x_1943_, 0, v___x_1942_);
    leanh::lean_ctor_set(v___x_1943_, 1, v___x_1942_);
    leanh::lean_ctor_set(v___x_1943_, 2, v___x_1942_);
    leanh::lean_ctor_set(v___x_1943_, 3, v___x_1942_);
    leanh::lean_ctor_set(v___x_1943_, 4, v___x_1942_);
    return v___x_1943_;
}
pub unsafe fn _init_l_Std_Async_System_instInhabitedCPUTimes_default()
-> *mut leanh::LeanObject {
    let mut v___x_1944_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1944_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Async_System_instInhabitedCPUTimes_default___closed__0),
        core::ptr::addr_of_mut!(l_Std_Async_System_instInhabitedCPUTimes_default___closed__0_once),
        _init_l_Std_Async_System_instInhabitedCPUTimes_default___closed__0,
    );
    return v___x_1944_;
}
pub unsafe fn _init_l_Std_Async_System_instInhabitedCPUTimes() -> *mut leanh::LeanObject {
    let mut v___x_1945_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1945_ = l_Std_Async_System_instInhabitedCPUTimes_default;
    return v___x_1945_;
}
pub unsafe fn l_Std_Async_System_instDecidableEqCPUTimes_decEq(
    mut v_x_1946_: *mut leanh::LeanObject,
    mut v_x_1947_: *mut leanh::LeanObject,
) -> u8 {
    let mut v_userTime_1948_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_niceTime_1949_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_systemTime_1950_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_idleTime_1951_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_interruptTime_1952_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_userTime_1953_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_niceTime_1954_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_systemTime_1955_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_idleTime_1956_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_interruptTime_1957_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1958_: u8 = 0;
    v_userTime_1948_ = leanh::lean_ctor_get(v_x_1946_, 0);
    v_niceTime_1949_ = leanh::lean_ctor_get(v_x_1946_, 1);
    v_systemTime_1950_ = leanh::lean_ctor_get(v_x_1946_, 2);
    v_idleTime_1951_ = leanh::lean_ctor_get(v_x_1946_, 3);
    v_interruptTime_1952_ = leanh::lean_ctor_get(v_x_1946_, 4);
    v_userTime_1953_ = leanh::lean_ctor_get(v_x_1947_, 0);
    v_niceTime_1954_ = leanh::lean_ctor_get(v_x_1947_, 1);
    v_systemTime_1955_ = leanh::lean_ctor_get(v_x_1947_, 2);
    v_idleTime_1956_ = leanh::lean_ctor_get(v_x_1947_, 3);
    v_interruptTime_1957_ = leanh::lean_ctor_get(v_x_1947_, 4);
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
    mut v_x_1963_: *mut leanh::LeanObject,
    mut v_x_1964_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1965_: u8 = 0;
    let mut v_r_1966_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1965_ = l_Std_Async_System_instDecidableEqCPUTimes_decEq(v_x_1963_, v_x_1964_);
    leanh::lean_dec_ref(v_x_1964_);
    leanh::lean_dec_ref(v_x_1963_);
    v_r_1966_ = leanh::lean_box((v_res_1965_) as usize);
    return v_r_1966_;
}
pub unsafe fn l_Std_Async_System_instDecidableEqCPUTimes(
    mut v_x_1967_: *mut leanh::LeanObject,
    mut v_x_1968_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_1969_: u8 = 0;
    v___x_1969_ = l_Std_Async_System_instDecidableEqCPUTimes_decEq(v_x_1967_, v_x_1968_);
    return v___x_1969_;
}
pub unsafe fn l_Std_Async_System_instDecidableEqCPUTimes___boxed(
    mut v_x_1970_: *mut leanh::LeanObject,
    mut v_x_1971_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1972_: u8 = 0;
    let mut v_r_1973_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1972_ = l_Std_Async_System_instDecidableEqCPUTimes(v_x_1970_, v_x_1971_);
    leanh::lean_dec_ref(v_x_1971_);
    leanh::lean_dec_ref(v_x_1970_);
    v_r_1973_ = leanh::lean_box((v_res_1972_) as usize);
    return v_r_1973_;
}
pub unsafe fn _init_l_Std_Async_System_instReprCPUTimes_repr___redArg___closed__8()
-> *mut leanh::LeanObject {
    let mut v___x_1989_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1990_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1989_ = leanh::lean_unsigned_to_nat(14);
    v___x_1990_ = lean_nat_to_int(v___x_1989_);
    return v___x_1990_;
}
pub unsafe fn _init_l_Std_Async_System_instReprCPUTimes_repr___redArg___closed__13()
-> *mut leanh::LeanObject {
    let mut v___x_1997_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1998_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1997_ = leanh::lean_unsigned_to_nat(17);
    v___x_1998_ = lean_nat_to_int(v___x_1997_);
    return v___x_1998_;
}
pub unsafe fn l_Std_Async_System_instReprCPUTimes_repr___redArg(
    mut v_x_1999_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_userTime_2000_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_niceTime_2001_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_systemTime_2002_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_idleTime_2003_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_interruptTime_2004_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2005_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2006_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2007_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2008_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2009_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2010_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2011_: u8 = 0;
    let mut v___x_2012_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2013_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2014_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2015_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2016_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2017_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2018_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2019_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2020_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2021_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2022_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2023_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2024_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2025_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2026_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2027_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2028_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2029_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2030_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2031_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2032_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2033_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2034_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2035_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2036_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2037_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2038_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2039_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2040_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2041_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2042_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2043_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2044_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2045_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2046_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2047_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2048_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2049_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2050_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2051_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2052_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2053_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2054_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2055_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2056_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2057_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2058_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2059_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2060_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_userTime_2000_ = leanh::lean_ctor_get(v_x_1999_, 0);
    v_niceTime_2001_ = leanh::lean_ctor_get(v_x_1999_, 1);
    v_systemTime_2002_ = leanh::lean_ctor_get(v_x_1999_, 2);
    v_idleTime_2003_ = leanh::lean_ctor_get(v_x_1999_, 3);
    v_interruptTime_2004_ = leanh::lean_ctor_get(v_x_1999_, 4);
    v___x_2005_ = l_Std_Async_System_instReprSystemUser_repr___redArg___closed__5;
    v___x_2006_ = l_Std_Async_System_instReprCPUTimes_repr___redArg___closed__3;
    v___x_2007_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Async_System_instReprSystemUser_repr___redArg___closed__7),
        core::ptr::addr_of_mut!(
            l_Std_Async_System_instReprSystemUser_repr___redArg___closed__7_once
        ),
        _init_l_Std_Async_System_instReprSystemUser_repr___redArg___closed__7,
    );
    v___x_2008_ = leanh::lean_unsigned_to_nat(0);
    v___x_2009_ = l_Std_Time_Millisecond_instReprOrdinal___lam__0(v_userTime_2000_, v___x_2008_);
    v___x_2010_ = leanh::lean_alloc_ctor(4, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_2010_, 0, v___x_2007_);
    leanh::lean_ctor_set(v___x_2010_, 1, v___x_2009_);
    v___x_2011_ = 0;
    v___x_2012_ = leanh::lean_alloc_ctor(6, 1, (1) as u32);
    leanh::lean_ctor_set(v___x_2012_, 0, v___x_2010_);
    leanh::lean_ctor_set_uint8(
        v___x_2012_,
        (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
        v___x_2011_,
    );
    v___x_2013_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_2013_, 0, v___x_2006_);
    leanh::lean_ctor_set(v___x_2013_, 1, v___x_2012_);
    v___x_2014_ = l_Std_Async_System_instReprSystemUser_repr___redArg___closed__9;
    v___x_2015_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_2015_, 0, v___x_2013_);
    leanh::lean_ctor_set(v___x_2015_, 1, v___x_2014_);
    v___x_2016_ = leanh::lean_box(1);
    v___x_2017_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_2017_, 0, v___x_2015_);
    leanh::lean_ctor_set(v___x_2017_, 1, v___x_2016_);
    v___x_2018_ = l_Std_Async_System_instReprCPUTimes_repr___redArg___closed__5;
    v___x_2019_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_2019_, 0, v___x_2017_);
    leanh::lean_ctor_set(v___x_2019_, 1, v___x_2018_);
    v___x_2020_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_2020_, 0, v___x_2019_);
    leanh::lean_ctor_set(v___x_2020_, 1, v___x_2005_);
    v___x_2021_ = l_Std_Time_Millisecond_instReprOrdinal___lam__0(v_niceTime_2001_, v___x_2008_);
    v___x_2022_ = leanh::lean_alloc_ctor(4, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_2022_, 0, v___x_2007_);
    leanh::lean_ctor_set(v___x_2022_, 1, v___x_2021_);
    v___x_2023_ = leanh::lean_alloc_ctor(6, 1, (1) as u32);
    leanh::lean_ctor_set(v___x_2023_, 0, v___x_2022_);
    leanh::lean_ctor_set_uint8(
        v___x_2023_,
        (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
        v___x_2011_,
    );
    v___x_2024_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_2024_, 0, v___x_2020_);
    leanh::lean_ctor_set(v___x_2024_, 1, v___x_2023_);
    v___x_2025_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_2025_, 0, v___x_2024_);
    leanh::lean_ctor_set(v___x_2025_, 1, v___x_2014_);
    v___x_2026_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_2026_, 0, v___x_2025_);
    leanh::lean_ctor_set(v___x_2026_, 1, v___x_2016_);
    v___x_2027_ = l_Std_Async_System_instReprCPUTimes_repr___redArg___closed__7;
    v___x_2028_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_2028_, 0, v___x_2026_);
    leanh::lean_ctor_set(v___x_2028_, 1, v___x_2027_);
    v___x_2029_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_2029_, 0, v___x_2028_);
    leanh::lean_ctor_set(v___x_2029_, 1, v___x_2005_);
    v___x_2030_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Async_System_instReprCPUTimes_repr___redArg___closed__8),
        core::ptr::addr_of_mut!(l_Std_Async_System_instReprCPUTimes_repr___redArg___closed__8_once),
        _init_l_Std_Async_System_instReprCPUTimes_repr___redArg___closed__8,
    );
    v___x_2031_ = l_Std_Time_Millisecond_instReprOrdinal___lam__0(v_systemTime_2002_, v___x_2008_);
    v___x_2032_ = leanh::lean_alloc_ctor(4, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_2032_, 0, v___x_2030_);
    leanh::lean_ctor_set(v___x_2032_, 1, v___x_2031_);
    v___x_2033_ = leanh::lean_alloc_ctor(6, 1, (1) as u32);
    leanh::lean_ctor_set(v___x_2033_, 0, v___x_2032_);
    leanh::lean_ctor_set_uint8(
        v___x_2033_,
        (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
        v___x_2011_,
    );
    v___x_2034_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_2034_, 0, v___x_2029_);
    leanh::lean_ctor_set(v___x_2034_, 1, v___x_2033_);
    v___x_2035_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_2035_, 0, v___x_2034_);
    leanh::lean_ctor_set(v___x_2035_, 1, v___x_2014_);
    v___x_2036_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_2036_, 0, v___x_2035_);
    leanh::lean_ctor_set(v___x_2036_, 1, v___x_2016_);
    v___x_2037_ = l_Std_Async_System_instReprCPUTimes_repr___redArg___closed__10;
    v___x_2038_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_2038_, 0, v___x_2036_);
    leanh::lean_ctor_set(v___x_2038_, 1, v___x_2037_);
    v___x_2039_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_2039_, 0, v___x_2038_);
    leanh::lean_ctor_set(v___x_2039_, 1, v___x_2005_);
    v___x_2040_ = l_Std_Time_Millisecond_instReprOrdinal___lam__0(v_idleTime_2003_, v___x_2008_);
    v___x_2041_ = leanh::lean_alloc_ctor(4, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_2041_, 0, v___x_2007_);
    leanh::lean_ctor_set(v___x_2041_, 1, v___x_2040_);
    v___x_2042_ = leanh::lean_alloc_ctor(6, 1, (1) as u32);
    leanh::lean_ctor_set(v___x_2042_, 0, v___x_2041_);
    leanh::lean_ctor_set_uint8(
        v___x_2042_,
        (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
        v___x_2011_,
    );
    v___x_2043_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_2043_, 0, v___x_2039_);
    leanh::lean_ctor_set(v___x_2043_, 1, v___x_2042_);
    v___x_2044_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_2044_, 0, v___x_2043_);
    leanh::lean_ctor_set(v___x_2044_, 1, v___x_2014_);
    v___x_2045_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_2045_, 0, v___x_2044_);
    leanh::lean_ctor_set(v___x_2045_, 1, v___x_2016_);
    v___x_2046_ = l_Std_Async_System_instReprCPUTimes_repr___redArg___closed__12;
    v___x_2047_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_2047_, 0, v___x_2045_);
    leanh::lean_ctor_set(v___x_2047_, 1, v___x_2046_);
    v___x_2048_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_2048_, 0, v___x_2047_);
    leanh::lean_ctor_set(v___x_2048_, 1, v___x_2005_);
    v___x_2049_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Async_System_instReprCPUTimes_repr___redArg___closed__13),
        core::ptr::addr_of_mut!(
            l_Std_Async_System_instReprCPUTimes_repr___redArg___closed__13_once
        ),
        _init_l_Std_Async_System_instReprCPUTimes_repr___redArg___closed__13,
    );
    v___x_2050_ =
        l_Std_Time_Millisecond_instReprOrdinal___lam__0(v_interruptTime_2004_, v___x_2008_);
    v___x_2051_ = leanh::lean_alloc_ctor(4, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_2051_, 0, v___x_2049_);
    leanh::lean_ctor_set(v___x_2051_, 1, v___x_2050_);
    v___x_2052_ = leanh::lean_alloc_ctor(6, 1, (1) as u32);
    leanh::lean_ctor_set(v___x_2052_, 0, v___x_2051_);
    leanh::lean_ctor_set_uint8(
        v___x_2052_,
        (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
        v___x_2011_,
    );
    v___x_2053_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_2053_, 0, v___x_2048_);
    leanh::lean_ctor_set(v___x_2053_, 1, v___x_2052_);
    v___x_2054_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Async_System_instReprSystemUser_repr___redArg___closed__23),
        core::ptr::addr_of_mut!(
            l_Std_Async_System_instReprSystemUser_repr___redArg___closed__23_once
        ),
        _init_l_Std_Async_System_instReprSystemUser_repr___redArg___closed__23,
    );
    v___x_2055_ = l_Std_Async_System_instReprSystemUser_repr___redArg___closed__24;
    v___x_2056_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_2056_, 0, v___x_2055_);
    leanh::lean_ctor_set(v___x_2056_, 1, v___x_2053_);
    v___x_2057_ = l_Std_Async_System_instReprSystemUser_repr___redArg___closed__25;
    v___x_2058_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_2058_, 0, v___x_2056_);
    leanh::lean_ctor_set(v___x_2058_, 1, v___x_2057_);
    v___x_2059_ = leanh::lean_alloc_ctor(4, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_2059_, 0, v___x_2054_);
    leanh::lean_ctor_set(v___x_2059_, 1, v___x_2058_);
    v___x_2060_ = leanh::lean_alloc_ctor(6, 1, (1) as u32);
    leanh::lean_ctor_set(v___x_2060_, 0, v___x_2059_);
    leanh::lean_ctor_set_uint8(
        v___x_2060_,
        (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
        v___x_2011_,
    );
    return v___x_2060_;
}
pub unsafe fn l_Std_Async_System_instReprCPUTimes_repr___redArg___boxed(
    mut v_x_2061_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2062_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2062_ = l_Std_Async_System_instReprCPUTimes_repr___redArg(v_x_2061_);
    leanh::lean_dec_ref(v_x_2061_);
    return v_res_2062_;
}
pub unsafe fn l_Std_Async_System_instReprCPUTimes_repr(
    mut v_x_2063_: *mut leanh::LeanObject,
    mut v_prec_2064_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2065_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2065_ = l_Std_Async_System_instReprCPUTimes_repr___redArg(v_x_2063_);
    return v___x_2065_;
}
pub unsafe fn l_Std_Async_System_instReprCPUTimes_repr___boxed(
    mut v_x_2066_: *mut leanh::LeanObject,
    mut v_prec_2067_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2068_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2068_ = l_Std_Async_System_instReprCPUTimes_repr(v_x_2066_, v_prec_2067_);
    leanh::lean_dec(v_prec_2067_);
    leanh::lean_dec_ref(v_x_2066_);
    return v_res_2068_;
}
pub unsafe fn _init_l_Std_Async_System_instInhabitedCPUInfo_default___closed__0()
-> *mut leanh::LeanObject {
    let mut v___x_2071_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2072_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2073_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2074_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2071_ = l_Std_Async_System_instInhabitedCPUTimes_default;
    v___x_2072_ = leanh::lean_unsigned_to_nat(0);
    v___x_2073_ = l_Std_Async_System_instInhabitedSystemUser_default___closed__0;
    v___x_2074_ = leanh::lean_alloc_ctor(0, 3, (0) as u32);
    leanh::lean_ctor_set(v___x_2074_, 0, v___x_2073_);
    leanh::lean_ctor_set(v___x_2074_, 1, v___x_2072_);
    leanh::lean_ctor_set(v___x_2074_, 2, v___x_2071_);
    return v___x_2074_;
}
pub unsafe fn _init_l_Std_Async_System_instInhabitedCPUInfo_default()
-> *mut leanh::LeanObject {
    let mut v___x_2075_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2075_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Async_System_instInhabitedCPUInfo_default___closed__0),
        core::ptr::addr_of_mut!(l_Std_Async_System_instInhabitedCPUInfo_default___closed__0_once),
        _init_l_Std_Async_System_instInhabitedCPUInfo_default___closed__0,
    );
    return v___x_2075_;
}
pub unsafe fn _init_l_Std_Async_System_instInhabitedCPUInfo() -> *mut leanh::LeanObject {
    let mut v___x_2076_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2076_ = l_Std_Async_System_instInhabitedCPUInfo_default;
    return v___x_2076_;
}
pub unsafe fn l_Std_Async_System_instDecidableEqCPUInfo_decEq(
    mut v_x_2077_: *mut leanh::LeanObject,
    mut v_x_2078_: *mut leanh::LeanObject,
) -> u8 {
    let mut v_model_2079_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_speed_2080_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_times_2081_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_model_2082_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_speed_2083_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_times_2084_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2085_: u8 = 0;
    v_model_2079_ = leanh::lean_ctor_get(v_x_2077_, 0);
    v_speed_2080_ = leanh::lean_ctor_get(v_x_2077_, 1);
    v_times_2081_ = leanh::lean_ctor_get(v_x_2077_, 2);
    v_model_2082_ = leanh::lean_ctor_get(v_x_2078_, 0);
    v_speed_2083_ = leanh::lean_ctor_get(v_x_2078_, 1);
    v_times_2084_ = leanh::lean_ctor_get(v_x_2078_, 2);
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
    mut v_x_2088_: *mut leanh::LeanObject,
    mut v_x_2089_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2090_: u8 = 0;
    let mut v_r_2091_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2090_ = l_Std_Async_System_instDecidableEqCPUInfo_decEq(v_x_2088_, v_x_2089_);
    leanh::lean_dec_ref(v_x_2089_);
    leanh::lean_dec_ref(v_x_2088_);
    v_r_2091_ = leanh::lean_box((v_res_2090_) as usize);
    return v_r_2091_;
}
pub unsafe fn l_Std_Async_System_instDecidableEqCPUInfo(
    mut v_x_2092_: *mut leanh::LeanObject,
    mut v_x_2093_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_2094_: u8 = 0;
    v___x_2094_ = l_Std_Async_System_instDecidableEqCPUInfo_decEq(v_x_2092_, v_x_2093_);
    return v___x_2094_;
}
pub unsafe fn l_Std_Async_System_instDecidableEqCPUInfo___boxed(
    mut v_x_2095_: *mut leanh::LeanObject,
    mut v_x_2096_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2097_: u8 = 0;
    let mut v_r_2098_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2097_ = l_Std_Async_System_instDecidableEqCPUInfo(v_x_2095_, v_x_2096_);
    leanh::lean_dec_ref(v_x_2096_);
    leanh::lean_dec_ref(v_x_2095_);
    v_r_2098_ = leanh::lean_box((v_res_2097_) as usize);
    return v_r_2098_;
}
pub unsafe fn l_Std_Async_System_instReprCPUInfo_repr___redArg(
    mut v_x_2114_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_model_2115_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_speed_2116_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_times_2117_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2118_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2119_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2120_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2121_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2122_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2123_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2124_: u8 = 0;
    let mut v___x_2125_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2126_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2127_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2128_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2129_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2130_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2131_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2132_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2133_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2134_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2135_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2136_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2137_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2138_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2139_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2140_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2141_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2142_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2143_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2144_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2145_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2146_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2147_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2148_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2149_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2150_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2151_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2152_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2153_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2154_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_model_2115_ = leanh::lean_ctor_get(v_x_2114_, 0);
    leanh::lean_inc_ref(v_model_2115_);
    v_speed_2116_ = leanh::lean_ctor_get(v_x_2114_, 1);
    leanh::lean_inc(v_speed_2116_);
    v_times_2117_ = leanh::lean_ctor_get(v_x_2114_, 2);
    leanh::lean_inc_ref(v_times_2117_);
    leanh::lean_dec_ref(v_x_2114_);
    v___x_2118_ = l_Std_Async_System_instReprSystemUser_repr___redArg___closed__5;
    v___x_2119_ = l_Std_Async_System_instReprCPUInfo_repr___redArg___closed__3;
    v___x_2120_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Async_System_instReprSystemUser_repr___redArg___closed__18),
        core::ptr::addr_of_mut!(
            l_Std_Async_System_instReprSystemUser_repr___redArg___closed__18_once
        ),
        _init_l_Std_Async_System_instReprSystemUser_repr___redArg___closed__18,
    );
    v___x_2121_ = l_String_quote(v_model_2115_);
    v___x_2122_ = leanh::lean_alloc_ctor(3, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_2122_, 0, v___x_2121_);
    v___x_2123_ = leanh::lean_alloc_ctor(4, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_2123_, 0, v___x_2120_);
    leanh::lean_ctor_set(v___x_2123_, 1, v___x_2122_);
    v___x_2124_ = 0;
    v___x_2125_ = leanh::lean_alloc_ctor(6, 1, (1) as u32);
    leanh::lean_ctor_set(v___x_2125_, 0, v___x_2123_);
    leanh::lean_ctor_set_uint8(
        v___x_2125_,
        (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
        v___x_2124_,
    );
    v___x_2126_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_2126_, 0, v___x_2119_);
    leanh::lean_ctor_set(v___x_2126_, 1, v___x_2125_);
    v___x_2127_ = l_Std_Async_System_instReprSystemUser_repr___redArg___closed__9;
    v___x_2128_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_2128_, 0, v___x_2126_);
    leanh::lean_ctor_set(v___x_2128_, 1, v___x_2127_);
    v___x_2129_ = leanh::lean_box(1);
    v___x_2130_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_2130_, 0, v___x_2128_);
    leanh::lean_ctor_set(v___x_2130_, 1, v___x_2129_);
    v___x_2131_ = l_Std_Async_System_instReprCPUInfo_repr___redArg___closed__5;
    v___x_2132_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_2132_, 0, v___x_2130_);
    leanh::lean_ctor_set(v___x_2132_, 1, v___x_2131_);
    v___x_2133_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_2133_, 0, v___x_2132_);
    leanh::lean_ctor_set(v___x_2133_, 1, v___x_2118_);
    v___x_2134_ = l_Nat_reprFast(v_speed_2116_);
    v___x_2135_ = leanh::lean_alloc_ctor(3, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_2135_, 0, v___x_2134_);
    v___x_2136_ = leanh::lean_alloc_ctor(4, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_2136_, 0, v___x_2120_);
    leanh::lean_ctor_set(v___x_2136_, 1, v___x_2135_);
    v___x_2137_ = leanh::lean_alloc_ctor(6, 1, (1) as u32);
    leanh::lean_ctor_set(v___x_2137_, 0, v___x_2136_);
    leanh::lean_ctor_set_uint8(
        v___x_2137_,
        (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
        v___x_2124_,
    );
    v___x_2138_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_2138_, 0, v___x_2133_);
    leanh::lean_ctor_set(v___x_2138_, 1, v___x_2137_);
    v___x_2139_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_2139_, 0, v___x_2138_);
    leanh::lean_ctor_set(v___x_2139_, 1, v___x_2127_);
    v___x_2140_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_2140_, 0, v___x_2139_);
    leanh::lean_ctor_set(v___x_2140_, 1, v___x_2129_);
    v___x_2141_ = l_Std_Async_System_instReprCPUInfo_repr___redArg___closed__7;
    v___x_2142_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_2142_, 0, v___x_2140_);
    leanh::lean_ctor_set(v___x_2142_, 1, v___x_2141_);
    v___x_2143_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_2143_, 0, v___x_2142_);
    leanh::lean_ctor_set(v___x_2143_, 1, v___x_2118_);
    v___x_2144_ = l_Std_Async_System_instReprCPUTimes_repr___redArg(v_times_2117_);
    leanh::lean_dec_ref(v_times_2117_);
    v___x_2145_ = leanh::lean_alloc_ctor(4, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_2145_, 0, v___x_2120_);
    leanh::lean_ctor_set(v___x_2145_, 1, v___x_2144_);
    v___x_2146_ = leanh::lean_alloc_ctor(6, 1, (1) as u32);
    leanh::lean_ctor_set(v___x_2146_, 0, v___x_2145_);
    leanh::lean_ctor_set_uint8(
        v___x_2146_,
        (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
        v___x_2124_,
    );
    v___x_2147_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_2147_, 0, v___x_2143_);
    leanh::lean_ctor_set(v___x_2147_, 1, v___x_2146_);
    v___x_2148_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Async_System_instReprSystemUser_repr___redArg___closed__23),
        core::ptr::addr_of_mut!(
            l_Std_Async_System_instReprSystemUser_repr___redArg___closed__23_once
        ),
        _init_l_Std_Async_System_instReprSystemUser_repr___redArg___closed__23,
    );
    v___x_2149_ = l_Std_Async_System_instReprSystemUser_repr___redArg___closed__24;
    v___x_2150_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_2150_, 0, v___x_2149_);
    leanh::lean_ctor_set(v___x_2150_, 1, v___x_2147_);
    v___x_2151_ = l_Std_Async_System_instReprSystemUser_repr___redArg___closed__25;
    v___x_2152_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_2152_, 0, v___x_2150_);
    leanh::lean_ctor_set(v___x_2152_, 1, v___x_2151_);
    v___x_2153_ = leanh::lean_alloc_ctor(4, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_2153_, 0, v___x_2148_);
    leanh::lean_ctor_set(v___x_2153_, 1, v___x_2152_);
    v___x_2154_ = leanh::lean_alloc_ctor(6, 1, (1) as u32);
    leanh::lean_ctor_set(v___x_2154_, 0, v___x_2153_);
    leanh::lean_ctor_set_uint8(
        v___x_2154_,
        (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
        v___x_2124_,
    );
    return v___x_2154_;
}
pub unsafe fn l_Std_Async_System_instReprCPUInfo_repr(
    mut v_x_2155_: *mut leanh::LeanObject,
    mut v_prec_2156_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2157_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2157_ = l_Std_Async_System_instReprCPUInfo_repr___redArg(v_x_2155_);
    return v___x_2157_;
}
pub unsafe fn l_Std_Async_System_instReprCPUInfo_repr___boxed(
    mut v_x_2158_: *mut leanh::LeanObject,
    mut v_prec_2159_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2160_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2160_ = l_Std_Async_System_instReprCPUInfo_repr(v_x_2158_, v_prec_2159_);
    leanh::lean_dec(v_prec_2159_);
    return v_res_2160_;
}
pub unsafe fn _init_l_Std_Async_System_instReprOSInfo_repr___redArg___closed__4()
-> *mut leanh::LeanObject {
    let mut v___x_2172_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2173_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2172_ = leanh::lean_unsigned_to_nat(8);
    v___x_2173_ = lean_nat_to_int(v___x_2172_);
    return v___x_2173_;
}
pub unsafe fn l_Std_Async_System_instReprOSInfo_repr___redArg(
    mut v_x_2183_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_name_2184_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_release_2185_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_version_2186_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_machine_2187_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2188_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2189_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2190_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2191_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2192_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2193_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2194_: u8 = 0;
    let mut v___x_2195_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2196_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2197_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2198_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2199_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2200_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2201_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2202_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2203_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2204_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2205_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2206_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2207_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2208_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2209_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2210_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2211_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2212_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2213_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2214_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2215_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2216_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2217_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2218_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2219_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2220_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2221_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2222_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2223_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2224_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2225_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2226_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2227_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2228_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2229_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2230_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2231_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2232_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2233_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2234_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2235_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2236_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_name_2184_ = leanh::lean_ctor_get(v_x_2183_, 0);
    leanh::lean_inc_ref(v_name_2184_);
    v_release_2185_ = leanh::lean_ctor_get(v_x_2183_, 1);
    leanh::lean_inc_ref(v_release_2185_);
    v_version_2186_ = leanh::lean_ctor_get(v_x_2183_, 2);
    leanh::lean_inc_ref(v_version_2186_);
    v_machine_2187_ = leanh::lean_ctor_get(v_x_2183_, 3);
    leanh::lean_inc_ref(v_machine_2187_);
    leanh::lean_dec_ref(v_x_2183_);
    v___x_2188_ = l_Std_Async_System_instReprSystemUser_repr___redArg___closed__5;
    v___x_2189_ = l_Std_Async_System_instReprOSInfo_repr___redArg___closed__3;
    v___x_2190_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Async_System_instReprOSInfo_repr___redArg___closed__4),
        core::ptr::addr_of_mut!(l_Std_Async_System_instReprOSInfo_repr___redArg___closed__4_once),
        _init_l_Std_Async_System_instReprOSInfo_repr___redArg___closed__4,
    );
    v___x_2191_ = l_String_quote(v_name_2184_);
    v___x_2192_ = leanh::lean_alloc_ctor(3, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_2192_, 0, v___x_2191_);
    v___x_2193_ = leanh::lean_alloc_ctor(4, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_2193_, 0, v___x_2190_);
    leanh::lean_ctor_set(v___x_2193_, 1, v___x_2192_);
    v___x_2194_ = 0;
    v___x_2195_ = leanh::lean_alloc_ctor(6, 1, (1) as u32);
    leanh::lean_ctor_set(v___x_2195_, 0, v___x_2193_);
    leanh::lean_ctor_set_uint8(
        v___x_2195_,
        (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
        v___x_2194_,
    );
    v___x_2196_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_2196_, 0, v___x_2189_);
    leanh::lean_ctor_set(v___x_2196_, 1, v___x_2195_);
    v___x_2197_ = l_Std_Async_System_instReprSystemUser_repr___redArg___closed__9;
    v___x_2198_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_2198_, 0, v___x_2196_);
    leanh::lean_ctor_set(v___x_2198_, 1, v___x_2197_);
    v___x_2199_ = leanh::lean_box(1);
    v___x_2200_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_2200_, 0, v___x_2198_);
    leanh::lean_ctor_set(v___x_2200_, 1, v___x_2199_);
    v___x_2201_ = l_Std_Async_System_instReprOSInfo_repr___redArg___closed__6;
    v___x_2202_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_2202_, 0, v___x_2200_);
    leanh::lean_ctor_set(v___x_2202_, 1, v___x_2201_);
    v___x_2203_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_2203_, 0, v___x_2202_);
    leanh::lean_ctor_set(v___x_2203_, 1, v___x_2188_);
    v___x_2204_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Async_System_instReprSystemUser_repr___redArg___closed__15),
        core::ptr::addr_of_mut!(
            l_Std_Async_System_instReprSystemUser_repr___redArg___closed__15_once
        ),
        _init_l_Std_Async_System_instReprSystemUser_repr___redArg___closed__15,
    );
    v___x_2205_ = l_String_quote(v_release_2185_);
    v___x_2206_ = leanh::lean_alloc_ctor(3, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_2206_, 0, v___x_2205_);
    v___x_2207_ = leanh::lean_alloc_ctor(4, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_2207_, 0, v___x_2204_);
    leanh::lean_ctor_set(v___x_2207_, 1, v___x_2206_);
    v___x_2208_ = leanh::lean_alloc_ctor(6, 1, (1) as u32);
    leanh::lean_ctor_set(v___x_2208_, 0, v___x_2207_);
    leanh::lean_ctor_set_uint8(
        v___x_2208_,
        (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
        v___x_2194_,
    );
    v___x_2209_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_2209_, 0, v___x_2203_);
    leanh::lean_ctor_set(v___x_2209_, 1, v___x_2208_);
    v___x_2210_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_2210_, 0, v___x_2209_);
    leanh::lean_ctor_set(v___x_2210_, 1, v___x_2197_);
    v___x_2211_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_2211_, 0, v___x_2210_);
    leanh::lean_ctor_set(v___x_2211_, 1, v___x_2199_);
    v___x_2212_ = l_Std_Async_System_instReprOSInfo_repr___redArg___closed__8;
    v___x_2213_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_2213_, 0, v___x_2211_);
    leanh::lean_ctor_set(v___x_2213_, 1, v___x_2212_);
    v___x_2214_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_2214_, 0, v___x_2213_);
    leanh::lean_ctor_set(v___x_2214_, 1, v___x_2188_);
    v___x_2215_ = l_String_quote(v_version_2186_);
    v___x_2216_ = leanh::lean_alloc_ctor(3, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_2216_, 0, v___x_2215_);
    v___x_2217_ = leanh::lean_alloc_ctor(4, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_2217_, 0, v___x_2204_);
    leanh::lean_ctor_set(v___x_2217_, 1, v___x_2216_);
    v___x_2218_ = leanh::lean_alloc_ctor(6, 1, (1) as u32);
    leanh::lean_ctor_set(v___x_2218_, 0, v___x_2217_);
    leanh::lean_ctor_set_uint8(
        v___x_2218_,
        (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
        v___x_2194_,
    );
    v___x_2219_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_2219_, 0, v___x_2214_);
    leanh::lean_ctor_set(v___x_2219_, 1, v___x_2218_);
    v___x_2220_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_2220_, 0, v___x_2219_);
    leanh::lean_ctor_set(v___x_2220_, 1, v___x_2197_);
    v___x_2221_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_2221_, 0, v___x_2220_);
    leanh::lean_ctor_set(v___x_2221_, 1, v___x_2199_);
    v___x_2222_ = l_Std_Async_System_instReprOSInfo_repr___redArg___closed__10;
    v___x_2223_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_2223_, 0, v___x_2221_);
    leanh::lean_ctor_set(v___x_2223_, 1, v___x_2222_);
    v___x_2224_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_2224_, 0, v___x_2223_);
    leanh::lean_ctor_set(v___x_2224_, 1, v___x_2188_);
    v___x_2225_ = l_String_quote(v_machine_2187_);
    v___x_2226_ = leanh::lean_alloc_ctor(3, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_2226_, 0, v___x_2225_);
    v___x_2227_ = leanh::lean_alloc_ctor(4, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_2227_, 0, v___x_2204_);
    leanh::lean_ctor_set(v___x_2227_, 1, v___x_2226_);
    v___x_2228_ = leanh::lean_alloc_ctor(6, 1, (1) as u32);
    leanh::lean_ctor_set(v___x_2228_, 0, v___x_2227_);
    leanh::lean_ctor_set_uint8(
        v___x_2228_,
        (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
        v___x_2194_,
    );
    v___x_2229_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_2229_, 0, v___x_2224_);
    leanh::lean_ctor_set(v___x_2229_, 1, v___x_2228_);
    v___x_2230_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Async_System_instReprSystemUser_repr___redArg___closed__23),
        core::ptr::addr_of_mut!(
            l_Std_Async_System_instReprSystemUser_repr___redArg___closed__23_once
        ),
        _init_l_Std_Async_System_instReprSystemUser_repr___redArg___closed__23,
    );
    v___x_2231_ = l_Std_Async_System_instReprSystemUser_repr___redArg___closed__24;
    v___x_2232_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_2232_, 0, v___x_2231_);
    leanh::lean_ctor_set(v___x_2232_, 1, v___x_2229_);
    v___x_2233_ = l_Std_Async_System_instReprSystemUser_repr___redArg___closed__25;
    v___x_2234_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_2234_, 0, v___x_2232_);
    leanh::lean_ctor_set(v___x_2234_, 1, v___x_2233_);
    v___x_2235_ = leanh::lean_alloc_ctor(4, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_2235_, 0, v___x_2230_);
    leanh::lean_ctor_set(v___x_2235_, 1, v___x_2234_);
    v___x_2236_ = leanh::lean_alloc_ctor(6, 1, (1) as u32);
    leanh::lean_ctor_set(v___x_2236_, 0, v___x_2235_);
    leanh::lean_ctor_set_uint8(
        v___x_2236_,
        (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
        v___x_2194_,
    );
    return v___x_2236_;
}
pub unsafe fn l_Std_Async_System_instReprOSInfo_repr(
    mut v_x_2237_: *mut leanh::LeanObject,
    mut v_prec_2238_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2239_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2239_ = l_Std_Async_System_instReprOSInfo_repr___redArg(v_x_2237_);
    return v___x_2239_;
}
pub unsafe fn l_Std_Async_System_instReprOSInfo_repr___boxed(
    mut v_x_2240_: *mut leanh::LeanObject,
    mut v_prec_2241_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2242_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2242_ = l_Std_Async_System_instReprOSInfo_repr(v_x_2240_, v_prec_2241_);
    leanh::lean_dec(v_prec_2241_);
    return v_res_2242_;
}
pub unsafe fn _init_l_Std_Async_System_instInhabitedEnvironment_default___closed__0()
-> *mut leanh::LeanObject {
    let mut v___x_2249_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2250_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2251_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2249_ = leanh::lean_box(0);
    v___x_2250_ = leanh::lean_unsigned_to_nat(16);
    v___x_2251_ = lean_mk_array(v___x_2250_, v___x_2249_);
    return v___x_2251_;
}
pub unsafe fn _init_l_Std_Async_System_instInhabitedEnvironment_default___closed__1()
-> *mut leanh::LeanObject {
    let mut v___x_2252_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2253_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2254_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2252_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Async_System_instInhabitedEnvironment_default___closed__0),
        core::ptr::addr_of_mut!(
            l_Std_Async_System_instInhabitedEnvironment_default___closed__0_once
        ),
        _init_l_Std_Async_System_instInhabitedEnvironment_default___closed__0,
    );
    v___x_2253_ = leanh::lean_unsigned_to_nat(0);
    v___x_2254_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_2254_, 0, v___x_2253_);
    leanh::lean_ctor_set(v___x_2254_, 1, v___x_2252_);
    return v___x_2254_;
}
pub unsafe fn _init_l_Std_Async_System_instInhabitedEnvironment_default()
-> *mut leanh::LeanObject {
    let mut v___x_2255_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2255_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Async_System_instInhabitedEnvironment_default___closed__1),
        core::ptr::addr_of_mut!(
            l_Std_Async_System_instInhabitedEnvironment_default___closed__1_once
        ),
        _init_l_Std_Async_System_instInhabitedEnvironment_default___closed__1,
    );
    return v___x_2255_;
}
pub unsafe fn _init_l_Std_Async_System_instInhabitedEnvironment() -> *mut leanh::LeanObject {
    let mut v___x_2256_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2256_ = l_Std_Async_System_instInhabitedEnvironment_default;
    return v___x_2256_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_foldrM___at___00Std_Async_System_instReprEnvironment_repr_spec__1(
    mut v_x_2257_: *mut leanh::LeanObject,
    mut v_x_2258_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_x_2258_) == 0 {
        leanh::lean_inc(v_x_2257_);
        return v_x_2257_;
    } else {
        let mut v_key_2259_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_value_2260_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_tail_2261_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2262_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2263_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2264_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_key_2259_ = leanh::lean_ctor_get(v_x_2258_, 0);
        v_value_2260_ = leanh::lean_ctor_get(v_x_2258_, 1);
        v_tail_2261_ = leanh::lean_ctor_get(v_x_2258_, 2);
        v___x_2262_ = l_Std_DHashMap_Internal_AssocList_foldrM___at___00Std_Async_System_instReprEnvironment_repr_spec__1(v_x_2257_, v_tail_2261_);
        leanh::lean_inc(v_value_2260_);
        leanh::lean_inc(v_key_2259_);
        v___x_2263_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
        leanh::lean_ctor_set(v___x_2263_, 0, v_key_2259_);
        leanh::lean_ctor_set(v___x_2263_, 1, v_value_2260_);
        v___x_2264_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
        leanh::lean_ctor_set(v___x_2264_, 0, v___x_2263_);
        leanh::lean_ctor_set(v___x_2264_, 1, v___x_2262_);
        return v___x_2264_;
    }
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_foldrM___at___00Std_Async_System_instReprEnvironment_repr_spec__1___boxed(
    mut v_x_2265_: *mut leanh::LeanObject,
    mut v_x_2266_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2267_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2267_ = l_Std_DHashMap_Internal_AssocList_foldrM___at___00Std_Async_System_instReprEnvironment_repr_spec__1(v_x_2265_, v_x_2266_);
    leanh::lean_dec(v_x_2266_);
    leanh::lean_dec(v_x_2265_);
    return v_res_2267_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Std_Async_System_instReprEnvironment_repr_spec__2(
    mut v_as_2268_: *mut leanh::LeanObject,
    mut v_i_2269_: usize,
    mut v_stop_2270_: usize,
    mut v_b_2271_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2272_: u8 = 0;
    let mut v___x_2273_: usize = 0;
    let mut v___x_2274_: usize = 0;
    let mut v___x_2275_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2276_: *mut leanh::LeanObject = core::ptr::null_mut();
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
                    leanh::lean_dec(v_b_2271_);
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
    mut v_as_2278_: *mut leanh::LeanObject,
    mut v_i_2279_: *mut leanh::LeanObject,
    mut v_stop_2280_: *mut leanh::LeanObject,
    mut v_b_2281_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_i_boxed_2282_: usize = 0;
    let mut v_stop_boxed_2283_: usize = 0;
    let mut v_res_2284_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_i_boxed_2282_ = leanh::lean_unbox_usize(v_i_2279_);
    leanh::lean_dec(v_i_2279_);
    v_stop_boxed_2283_ = leanh::lean_unbox_usize(v_stop_2280_);
    leanh::lean_dec(v_stop_2280_);
    v_res_2284_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Std_Async_System_instReprEnvironment_repr_spec__2(v_as_2278_, v_i_boxed_2282_, v_stop_boxed_2283_, v_b_2281_);
    leanh::lean_dec_ref(v_as_2278_);
    return v_res_2284_;
}
pub unsafe fn l_List_foldl___at___00Std_Format_joinSep___at___00Prod_repr___at___00List_repr___at___00Std_Async_System_instReprEnvironment_repr_spec__0_spec__0_spec__1_spec__4(
    mut v_x_2285_: *mut leanh::LeanObject,
    mut v_x_2286_: *mut leanh::LeanObject,
    mut v_x_2287_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_head_2288_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_2289_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2291_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2292_: u8 = 0;
    let mut v___x_2294_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2295_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2297_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2298_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_2287_) == 0 {
                    leanh::lean_dec(v_x_2285_);
                    return v_x_2286_;
                } else {
                    v_head_2288_ = leanh::lean_ctor_get(v_x_2287_, 0);
                    v_tail_2289_ = leanh::lean_ctor_get(v_x_2287_, 1);
                    v_isSharedCheck_2298_ = (!leanh::lean_is_exclusive(v_x_2287_)) as u8;
                    if v_isSharedCheck_2298_ == 0 {
                        v___x_2291_ = v_x_2287_;
                        v_isShared_2292_ = v_isSharedCheck_2298_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_tail_2289_);
                        leanh::lean_inc(v_head_2288_);
                        leanh::lean_dec(v_x_2287_);
                        v___x_2291_ = leanh::lean_box(0);
                        v_isShared_2292_ = v_isSharedCheck_2298_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                leanh::lean_inc(v_x_2285_);
                if v_isShared_2292_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_2291_, 5);
                    leanh::lean_ctor_set(v___x_2291_, 1, v_x_2285_);
                    leanh::lean_ctor_set(v___x_2291_, 0, v_x_2286_);
                    v___x_2294_ = v___x_2291_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2297_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2297_, 0, v_x_2286_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2297_, 1, v_x_2285_);
                    v___x_2294_ = v_reuseFailAlloc_2297_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_2295_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_2295_, 0, v___x_2294_);
                leanh::lean_ctor_set(v___x_2295_, 1, v_head_2288_);
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
    mut v_x_2299_: *mut leanh::LeanObject,
    mut v_x_2300_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_x_2299_) == 0 {
        let mut v___x_2301_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_x_2300_);
        v___x_2301_ = leanh::lean_box(0);
        return v___x_2301_;
    } else {
        let mut v_tail_2302_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_tail_2302_ = leanh::lean_ctor_get(v_x_2299_, 1);
        if leanh::lean_obj_tag(v_tail_2302_) == 0 {
            let mut v_head_2303_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_x_2300_);
            v_head_2303_ = leanh::lean_ctor_get(v_x_2299_, 0);
            leanh::lean_inc(v_head_2303_);
            leanh::lean_dec_ref_known(v_x_2299_, 2);
            return v_head_2303_;
        } else {
            let mut v_head_2304_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_2305_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_inc(v_tail_2302_);
            v_head_2304_ = leanh::lean_ctor_get(v_x_2299_, 0);
            leanh::lean_inc(v_head_2304_);
            leanh::lean_dec_ref_known(v_x_2299_, 2);
            v___x_2305_ = l_List_foldl___at___00Std_Format_joinSep___at___00Prod_repr___at___00List_repr___at___00Std_Async_System_instReprEnvironment_repr_spec__0_spec__0_spec__1_spec__4(v_x_2300_, v_head_2304_, v_tail_2302_);
            return v___x_2305_;
        }
    }
}
pub unsafe fn _init_l_Prod_repr___at___00List_repr___at___00Std_Async_System_instReprEnvironment_repr_spec__0_spec__0___redArg___closed__2()
-> *mut leanh::LeanObject {
    let mut v___x_2308_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2309_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2308_ = l_Prod_repr___at___00List_repr___at___00Std_Async_System_instReprEnvironment_repr_spec__0_spec__0___redArg___closed__0;
    v___x_2309_ = lean_string_length(v___x_2308_);
    return v___x_2309_;
}
pub unsafe fn _init_l_Prod_repr___at___00List_repr___at___00Std_Async_System_instReprEnvironment_repr_spec__0_spec__0___redArg___closed__3()
-> *mut leanh::LeanObject {
    let mut v___x_2310_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2311_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2310_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Prod_repr___at___00List_repr___at___00Std_Async_System_instReprEnvironment_repr_spec__0_spec__0___redArg___closed__2), core::ptr::addr_of_mut!(l_Prod_repr___at___00List_repr___at___00Std_Async_System_instReprEnvironment_repr_spec__0_spec__0___redArg___closed__2_once), _init_l_Prod_repr___at___00List_repr___at___00Std_Async_System_instReprEnvironment_repr_spec__0_spec__0___redArg___closed__2);
    v___x_2311_ = lean_nat_to_int(v___x_2310_);
    return v___x_2311_;
}
pub unsafe fn l_Prod_repr___at___00List_repr___at___00Std_Async_System_instReprEnvironment_repr_spec__0_spec__0___redArg(
    mut v_x_2316_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_fst_2317_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2318_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2320_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2321_: u8 = 0;
    let mut v___x_2322_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2323_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2324_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2326_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2327_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2328_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2329_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2330_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2331_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2332_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2333_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2334_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2335_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2336_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2337_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2338_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2339_: u8 = 0;
    let mut v___x_2340_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2341_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2342_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_fst_2317_ = leanh::lean_ctor_get(v_x_2316_, 0);
                v_snd_2318_ = leanh::lean_ctor_get(v_x_2316_, 1);
                v_isSharedCheck_2342_ = (!leanh::lean_is_exclusive(v_x_2316_)) as u8;
                if v_isSharedCheck_2342_ == 0 {
                    v___x_2320_ = v_x_2316_;
                    v_isShared_2321_ = v_isSharedCheck_2342_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_snd_2318_);
                    leanh::lean_inc(v_fst_2317_);
                    leanh::lean_dec(v_x_2316_);
                    v___x_2320_ = leanh::lean_box(0);
                    v_isShared_2321_ = v_isSharedCheck_2342_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_2322_ = l_String_quote(v_fst_2317_);
                v___x_2323_ = leanh::lean_alloc_ctor(3, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_2323_, 0, v___x_2322_);
                v___x_2324_ = leanh::lean_box(0);
                if v_isShared_2321_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_2320_, 1);
                    leanh::lean_ctor_set(v___x_2320_, 1, v___x_2324_);
                    leanh::lean_ctor_set(v___x_2320_, 0, v___x_2323_);
                    v___x_2326_ = v___x_2320_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2341_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2341_, 0, v___x_2323_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2341_, 1, v___x_2324_);
                    v___x_2326_ = v_reuseFailAlloc_2341_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_2327_ = l_String_quote(v_snd_2318_);
                v___x_2328_ = leanh::lean_alloc_ctor(3, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_2328_, 0, v___x_2327_);
                v___x_2329_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_2329_, 0, v___x_2328_);
                leanh::lean_ctor_set(v___x_2329_, 1, v___x_2326_);
                v___x_2330_ = l_List_reverse___redArg(v___x_2329_);
                v___x_2331_ = l_Array_repr___at___00Std_Async_System_instReprGroupInfo_repr_spec__0___closed__1;
                v___x_2332_ = l_Std_Format_joinSep___at___00Prod_repr___at___00List_repr___at___00Std_Async_System_instReprEnvironment_repr_spec__0_spec__0_spec__1(v___x_2330_, v___x_2331_);
                v___x_2333_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Prod_repr___at___00List_repr___at___00Std_Async_System_instReprEnvironment_repr_spec__0_spec__0___redArg___closed__3), core::ptr::addr_of_mut!(l_Prod_repr___at___00List_repr___at___00Std_Async_System_instReprEnvironment_repr_spec__0_spec__0___redArg___closed__3_once), _init_l_Prod_repr___at___00List_repr___at___00Std_Async_System_instReprEnvironment_repr_spec__0_spec__0___redArg___closed__3);
                v___x_2334_ = l_Prod_repr___at___00List_repr___at___00Std_Async_System_instReprEnvironment_repr_spec__0_spec__0___redArg___closed__4;
                v___x_2335_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_2335_, 0, v___x_2334_);
                leanh::lean_ctor_set(v___x_2335_, 1, v___x_2332_);
                v___x_2336_ = l_Prod_repr___at___00List_repr___at___00Std_Async_System_instReprEnvironment_repr_spec__0_spec__0___redArg___closed__5;
                v___x_2337_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_2337_, 0, v___x_2335_);
                leanh::lean_ctor_set(v___x_2337_, 1, v___x_2336_);
                v___x_2338_ = leanh::lean_alloc_ctor(4, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_2338_, 0, v___x_2333_);
                leanh::lean_ctor_set(v___x_2338_, 1, v___x_2337_);
                v___x_2339_ = 0;
                v___x_2340_ = leanh::lean_alloc_ctor(6, 1, (1) as u32);
                leanh::lean_ctor_set(v___x_2340_, 0, v___x_2338_);
                leanh::lean_ctor_set_uint8(
                    v___x_2340_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                    v___x_2339_,
                );
                return v___x_2340_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00List_repr___at___00Std_Async_System_instReprEnvironment_repr_spec__0_spec__1_spec__3_spec__7(
    mut v_x_2343_: *mut leanh::LeanObject,
    mut v_x_2344_: *mut leanh::LeanObject,
    mut v_x_2345_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_head_2346_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_2347_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2349_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2350_: u8 = 0;
    let mut v___x_2352_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2353_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2354_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2356_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2357_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_2345_) == 0 {
                    leanh::lean_dec(v_x_2343_);
                    return v_x_2344_;
                } else {
                    v_head_2346_ = leanh::lean_ctor_get(v_x_2345_, 0);
                    v_tail_2347_ = leanh::lean_ctor_get(v_x_2345_, 1);
                    v_isSharedCheck_2357_ = (!leanh::lean_is_exclusive(v_x_2345_)) as u8;
                    if v_isSharedCheck_2357_ == 0 {
                        v___x_2349_ = v_x_2345_;
                        v_isShared_2350_ = v_isSharedCheck_2357_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_tail_2347_);
                        leanh::lean_inc(v_head_2346_);
                        leanh::lean_dec(v_x_2345_);
                        v___x_2349_ = leanh::lean_box(0);
                        v_isShared_2350_ = v_isSharedCheck_2357_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                leanh::lean_inc(v_x_2343_);
                if v_isShared_2350_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_2349_, 5);
                    leanh::lean_ctor_set(v___x_2349_, 1, v_x_2343_);
                    leanh::lean_ctor_set(v___x_2349_, 0, v_x_2344_);
                    v___x_2352_ = v___x_2349_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2356_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2356_, 0, v_x_2344_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2356_, 1, v_x_2343_);
                    v___x_2352_ = v_reuseFailAlloc_2356_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_2353_ = l_Prod_repr___at___00List_repr___at___00Std_Async_System_instReprEnvironment_repr_spec__0_spec__0___redArg(v_head_2346_);
                v___x_2354_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_2354_, 0, v___x_2352_);
                leanh::lean_ctor_set(v___x_2354_, 1, v___x_2353_);
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
    mut v_x_2358_: *mut leanh::LeanObject,
    mut v_x_2359_: *mut leanh::LeanObject,
    mut v_x_2360_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_head_2361_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_2362_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2364_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2365_: u8 = 0;
    let mut v___x_2367_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2368_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2369_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2370_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2371_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2372_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_2360_) == 0 {
                    leanh::lean_dec(v_x_2358_);
                    return v_x_2359_;
                } else {
                    v_head_2361_ = leanh::lean_ctor_get(v_x_2360_, 0);
                    v_tail_2362_ = leanh::lean_ctor_get(v_x_2360_, 1);
                    v_isSharedCheck_2372_ = (!leanh::lean_is_exclusive(v_x_2360_)) as u8;
                    if v_isSharedCheck_2372_ == 0 {
                        v___x_2364_ = v_x_2360_;
                        v_isShared_2365_ = v_isSharedCheck_2372_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_tail_2362_);
                        leanh::lean_inc(v_head_2361_);
                        leanh::lean_dec(v_x_2360_);
                        v___x_2364_ = leanh::lean_box(0);
                        v_isShared_2365_ = v_isSharedCheck_2372_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                leanh::lean_inc(v_x_2358_);
                if v_isShared_2365_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_2364_, 5);
                    leanh::lean_ctor_set(v___x_2364_, 1, v_x_2358_);
                    leanh::lean_ctor_set(v___x_2364_, 0, v_x_2359_);
                    v___x_2367_ = v___x_2364_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2371_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2371_, 0, v_x_2359_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2371_, 1, v_x_2358_);
                    v___x_2367_ = v_reuseFailAlloc_2371_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_2368_ = l_Prod_repr___at___00List_repr___at___00Std_Async_System_instReprEnvironment_repr_spec__0_spec__0___redArg(v_head_2361_);
                v___x_2369_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_2369_, 0, v___x_2367_);
                leanh::lean_ctor_set(v___x_2369_, 1, v___x_2368_);
                v___x_2370_ = l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00List_repr___at___00Std_Async_System_instReprEnvironment_repr_spec__0_spec__1_spec__3_spec__7(v_x_2358_, v___x_2369_, v_tail_2362_);
                return v___x_2370_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Format_joinSep___at___00List_repr___at___00Std_Async_System_instReprEnvironment_repr_spec__0_spec__1(
    mut v_x_2373_: *mut leanh::LeanObject,
    mut v_x_2374_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_x_2373_) == 0 {
        let mut v___x_2375_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_x_2374_);
        v___x_2375_ = leanh::lean_box(0);
        return v___x_2375_;
    } else {
        let mut v_tail_2376_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_tail_2376_ = leanh::lean_ctor_get(v_x_2373_, 1);
        if leanh::lean_obj_tag(v_tail_2376_) == 0 {
            let mut v_head_2377_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_2378_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_x_2374_);
            v_head_2377_ = leanh::lean_ctor_get(v_x_2373_, 0);
            leanh::lean_inc(v_head_2377_);
            leanh::lean_dec_ref_known(v_x_2373_, 2);
            v___x_2378_ = l_Prod_repr___at___00List_repr___at___00Std_Async_System_instReprEnvironment_repr_spec__0_spec__0___redArg(v_head_2377_);
            return v___x_2378_;
        } else {
            let mut v_head_2379_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_2380_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_2381_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_inc(v_tail_2376_);
            v_head_2379_ = leanh::lean_ctor_get(v_x_2373_, 0);
            leanh::lean_inc(v_head_2379_);
            leanh::lean_dec_ref_known(v_x_2373_, 2);
            v___x_2380_ = l_Prod_repr___at___00List_repr___at___00Std_Async_System_instReprEnvironment_repr_spec__0_spec__0___redArg(v_head_2379_);
            v___x_2381_ = l_List_foldl___at___00Std_Format_joinSep___at___00List_repr___at___00Std_Async_System_instReprEnvironment_repr_spec__0_spec__1_spec__3(v_x_2374_, v___x_2380_, v_tail_2376_);
            return v___x_2381_;
        }
    }
}
pub unsafe fn _init_l_List_repr___at___00Std_Async_System_instReprEnvironment_repr_spec__0___redArg___closed__3()
-> *mut leanh::LeanObject {
    let mut v___x_2386_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2387_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2386_ =
        l_List_repr___at___00Std_Async_System_instReprEnvironment_repr_spec__0___redArg___closed__2;
    v___x_2387_ = lean_string_length(v___x_2386_);
    return v___x_2387_;
}
pub unsafe fn _init_l_List_repr___at___00Std_Async_System_instReprEnvironment_repr_spec__0___redArg___closed__4()
-> *mut leanh::LeanObject {
    let mut v___x_2388_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2389_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2388_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_List_repr___at___00Std_Async_System_instReprEnvironment_repr_spec__0___redArg___closed__3), core::ptr::addr_of_mut!(l_List_repr___at___00Std_Async_System_instReprEnvironment_repr_spec__0___redArg___closed__3_once), _init_l_List_repr___at___00Std_Async_System_instReprEnvironment_repr_spec__0___redArg___closed__3);
    v___x_2389_ = lean_nat_to_int(v___x_2388_);
    return v___x_2389_;
}
pub unsafe fn l_List_repr___at___00Std_Async_System_instReprEnvironment_repr_spec__0___redArg(
    mut v_a_2392_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_a_2392_) == 0 {
        let mut v___x_2393_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_2393_ = l_List_repr___at___00Std_Async_System_instReprEnvironment_repr_spec__0___redArg___closed__1;
        return v___x_2393_;
    } else {
        let mut v___x_2394_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2395_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2396_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2397_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2398_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2399_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2400_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2401_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2402_: u8 = 0;
        let mut v___x_2403_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_2394_ =
            l_Array_repr___at___00Std_Async_System_instReprGroupInfo_repr_spec__0___closed__1;
        v___x_2395_ = l_Std_Format_joinSep___at___00List_repr___at___00Std_Async_System_instReprEnvironment_repr_spec__0_spec__1(v_a_2392_, v___x_2394_);
        v___x_2396_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_List_repr___at___00Std_Async_System_instReprEnvironment_repr_spec__0___redArg___closed__4), core::ptr::addr_of_mut!(l_List_repr___at___00Std_Async_System_instReprEnvironment_repr_spec__0___redArg___closed__4_once), _init_l_List_repr___at___00Std_Async_System_instReprEnvironment_repr_spec__0___redArg___closed__4);
        v___x_2397_ = l_List_repr___at___00Std_Async_System_instReprEnvironment_repr_spec__0___redArg___closed__5;
        v___x_2398_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
        leanh::lean_ctor_set(v___x_2398_, 0, v___x_2397_);
        leanh::lean_ctor_set(v___x_2398_, 1, v___x_2395_);
        v___x_2399_ =
            l_Array_repr___at___00Std_Async_System_instReprGroupInfo_repr_spec__0___closed__6;
        v___x_2400_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
        leanh::lean_ctor_set(v___x_2400_, 0, v___x_2398_);
        leanh::lean_ctor_set(v___x_2400_, 1, v___x_2399_);
        v___x_2401_ = leanh::lean_alloc_ctor(4, 2, (0) as u32);
        leanh::lean_ctor_set(v___x_2401_, 0, v___x_2396_);
        leanh::lean_ctor_set(v___x_2401_, 1, v___x_2400_);
        v___x_2402_ = 0;
        v___x_2403_ = leanh::lean_alloc_ctor(6, 1, (1) as u32);
        leanh::lean_ctor_set(v___x_2403_, 0, v___x_2401_);
        leanh::lean_ctor_set_uint8(
            v___x_2403_,
            (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
            v___x_2402_,
        );
        return v___x_2403_;
    }
}
pub unsafe fn l_Std_Async_System_instReprEnvironment_repr___redArg(
    mut v_x_2416_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_buckets_2417_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2419_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2420_: u8 = 0;
    let mut v___x_2421_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2422_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2423_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2424_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2426_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2427_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2429_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2430_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2431_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2432_: u8 = 0;
    let mut v___x_2433_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2434_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2435_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2436_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2437_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2438_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2439_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2440_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2441_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2442_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2443_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2444_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2445_: u8 = 0;
    let mut v___x_2446_: usize = 0;
    let mut v___x_2447_: usize = 0;
    let mut v___x_2448_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2449_: u8 = 0;
    let mut v_unused_2450_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_buckets_2417_ = leanh::lean_ctor_get(v_x_2416_, 1);
                v_isSharedCheck_2449_ = (!leanh::lean_is_exclusive(v_x_2416_)) as u8;
                if v_isSharedCheck_2449_ == 0 {
                    v_unused_2450_ = leanh::lean_ctor_get(v_x_2416_, 0);
                    leanh::lean_dec(v_unused_2450_);
                    v___x_2419_ = v_x_2416_;
                    v_isShared_2420_ = v_isSharedCheck_2449_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_buckets_2417_);
                    leanh::lean_dec(v_x_2416_);
                    v___x_2419_ = leanh::lean_box(0);
                    v_isShared_2420_ = v_isSharedCheck_2449_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_2421_ = l_Std_Async_System_instReprEnvironment_repr___redArg___closed__3;
                v___x_2422_ = leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Std_Async_System_instReprGroupInfo_repr___redArg___closed__4
                    ),
                    core::ptr::addr_of_mut!(
                        l_Std_Async_System_instReprGroupInfo_repr___redArg___closed__4_once
                    ),
                    _init_l_Std_Async_System_instReprGroupInfo_repr___redArg___closed__4,
                );
                v___x_2423_ = leanh::lean_unsigned_to_nat(0);
                v___x_2424_ = l_Std_Async_System_instReprEnvironment_repr___redArg___closed__5;
                v___x_2443_ = leanh::lean_box(0);
                v___x_2444_ = lean_array_get_size(v_buckets_2417_);
                v___x_2445_ = lean_nat_dec_lt(v___x_2423_, v___x_2444_);
                if v___x_2445_ == 0 {
                    leanh::lean_dec_ref(v_buckets_2417_);
                    v___y_2426_ = v___x_2443_;
                    state = 2;
                    continue;
                } else {
                    v___x_2446_ = lean_usize_of_nat(v___x_2444_);
                    v___x_2447_ = 0usize;
                    v___x_2448_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Std_Async_System_instReprEnvironment_repr_spec__2(v_buckets_2417_, v___x_2446_, v___x_2447_, v___x_2443_);
                    leanh::lean_dec_ref(v_buckets_2417_);
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
                    leanh::lean_ctor_set_tag(v___x_2419_, 5);
                    leanh::lean_ctor_set(v___x_2419_, 1, v___x_2427_);
                    leanh::lean_ctor_set(v___x_2419_, 0, v___x_2424_);
                    v___x_2429_ = v___x_2419_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_2442_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2442_, 0, v___x_2424_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2442_, 1, v___x_2427_);
                    v___x_2429_ = v_reuseFailAlloc_2442_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_2430_ = l_Repr_addAppParen(v___x_2429_, v___x_2423_);
                v___x_2431_ = leanh::lean_alloc_ctor(4, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_2431_, 0, v___x_2422_);
                leanh::lean_ctor_set(v___x_2431_, 1, v___x_2430_);
                v___x_2432_ = 0;
                v___x_2433_ = leanh::lean_alloc_ctor(6, 1, (1) as u32);
                leanh::lean_ctor_set(v___x_2433_, 0, v___x_2431_);
                leanh::lean_ctor_set_uint8(
                    v___x_2433_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                    v___x_2432_,
                );
                v___x_2434_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_2434_, 0, v___x_2421_);
                leanh::lean_ctor_set(v___x_2434_, 1, v___x_2433_);
                v___x_2435_ = leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Std_Async_System_instReprSystemUser_repr___redArg___closed__23
                    ),
                    core::ptr::addr_of_mut!(
                        l_Std_Async_System_instReprSystemUser_repr___redArg___closed__23_once
                    ),
                    _init_l_Std_Async_System_instReprSystemUser_repr___redArg___closed__23,
                );
                v___x_2436_ = l_Std_Async_System_instReprSystemUser_repr___redArg___closed__24;
                v___x_2437_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_2437_, 0, v___x_2436_);
                leanh::lean_ctor_set(v___x_2437_, 1, v___x_2434_);
                v___x_2438_ = l_Std_Async_System_instReprSystemUser_repr___redArg___closed__25;
                v___x_2439_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_2439_, 0, v___x_2437_);
                leanh::lean_ctor_set(v___x_2439_, 1, v___x_2438_);
                v___x_2440_ = leanh::lean_alloc_ctor(4, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_2440_, 0, v___x_2435_);
                leanh::lean_ctor_set(v___x_2440_, 1, v___x_2439_);
                v___x_2441_ = leanh::lean_alloc_ctor(6, 1, (1) as u32);
                leanh::lean_ctor_set(v___x_2441_, 0, v___x_2440_);
                leanh::lean_ctor_set_uint8(
                    v___x_2441_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                    v___x_2432_,
                );
                return v___x_2441_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Async_System_instReprEnvironment_repr(
    mut v_x_2451_: *mut leanh::LeanObject,
    mut v_prec_2452_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2453_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2453_ = l_Std_Async_System_instReprEnvironment_repr___redArg(v_x_2451_);
    return v___x_2453_;
}
pub unsafe fn l_Std_Async_System_instReprEnvironment_repr___boxed(
    mut v_x_2454_: *mut leanh::LeanObject,
    mut v_prec_2455_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2456_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2456_ = l_Std_Async_System_instReprEnvironment_repr(v_x_2454_, v_prec_2455_);
    leanh::lean_dec(v_prec_2455_);
    return v_res_2456_;
}
pub unsafe fn l_List_repr___at___00Std_Async_System_instReprEnvironment_repr_spec__0(
    mut v_a_2457_: *mut leanh::LeanObject,
    mut v_n_2458_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2459_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2459_ =
        l_List_repr___at___00Std_Async_System_instReprEnvironment_repr_spec__0___redArg(v_a_2457_);
    return v___x_2459_;
}
pub unsafe fn l_List_repr___at___00Std_Async_System_instReprEnvironment_repr_spec__0___boxed(
    mut v_a_2460_: *mut leanh::LeanObject,
    mut v_n_2461_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2462_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2462_ = l_List_repr___at___00Std_Async_System_instReprEnvironment_repr_spec__0(
        v_a_2460_, v_n_2461_,
    );
    leanh::lean_dec(v_n_2461_);
    return v_res_2462_;
}
pub unsafe fn l_Prod_repr___at___00List_repr___at___00Std_Async_System_instReprEnvironment_repr_spec__0_spec__0(
    mut v_x_2463_: *mut leanh::LeanObject,
    mut v_x_2464_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2465_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2465_ = l_Prod_repr___at___00List_repr___at___00Std_Async_System_instReprEnvironment_repr_spec__0_spec__0___redArg(v_x_2463_);
    return v___x_2465_;
}
pub unsafe fn l_Prod_repr___at___00List_repr___at___00Std_Async_System_instReprEnvironment_repr_spec__0_spec__0___boxed(
    mut v_x_2466_: *mut leanh::LeanObject,
    mut v_x_2467_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2468_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2468_ = l_Prod_repr___at___00List_repr___at___00Std_Async_System_instReprEnvironment_repr_spec__0_spec__0(v_x_2466_, v_x_2467_);
    leanh::lean_dec(v_x_2467_);
    return v_res_2468_;
}
pub unsafe fn _init_l_Std_Async_System_Environment_get_x3f___closed__1()
-> *mut leanh::LeanObject {
    let mut v___x_2472_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2473_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2472_ = leanh::lean_alloc_closure(
        l_instDecidableEqString___boxed as *mut core::ffi::c_void,
        2,
        0,
    );
    v___f_2473_ = leanh::lean_alloc_closure(
        l_instBEqOfDecidableEq___redArg___lam__0___boxed as *mut core::ffi::c_void,
        3,
        1,
    );
    leanh::lean_closure_set(v___f_2473_, 0, v___x_2472_);
    return v___f_2473_;
}
pub unsafe fn l_Std_Async_System_Environment_get_x3f(
    mut v_env_2474_: *mut leanh::LeanObject,
    mut v_key_2475_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2476_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2477_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2478_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2476_ = l_Std_Async_System_Environment_get_x3f___closed__0;
    v___f_2477_ = leanh::lean_obj_once(
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
    mut v_env_2479_: *mut leanh::LeanObject,
    mut v_key_2480_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2481_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2481_ = l_Std_Async_System_Environment_get_x3f(v_env_2479_, v_key_2480_);
    leanh::lean_dec_ref(v_env_2479_);
    return v_res_2481_;
}
pub unsafe fn l_Std_Async_System_getSystemInfo() -> *mut leanh::LeanObject {
    let mut v___x_2483_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2484_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2486_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2487_: u8 = 0;
    let mut v_sysname_2488_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_release_2489_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_version_2490_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_machine_2491_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2493_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2494_: u8 = 0;
    let mut v___x_2496_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2498_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2499_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2500_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2501_: u8 = 0;
    let mut v_isSharedCheck_2502_: u8 = 0;
    let mut v_a_2503_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2505_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2506_: u8 = 0;
    let mut v___x_2508_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2509_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2510_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2483_ = lean_uv_os_uname();
                if leanh::lean_obj_tag(v___x_2483_) == 0 {
                    v_a_2484_ = leanh::lean_ctor_get(v___x_2483_, 0);
                    v_isSharedCheck_2502_ = (!leanh::lean_is_exclusive(v___x_2483_)) as u8;
                    if v_isSharedCheck_2502_ == 0 {
                        v___x_2486_ = v___x_2483_;
                        v_isShared_2487_ = v_isSharedCheck_2502_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_2484_);
                        leanh::lean_dec(v___x_2483_);
                        v___x_2486_ = leanh::lean_box(0);
                        v_isShared_2487_ = v_isSharedCheck_2502_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_2503_ = leanh::lean_ctor_get(v___x_2483_, 0);
                    v_isSharedCheck_2510_ = (!leanh::lean_is_exclusive(v___x_2483_)) as u8;
                    if v_isSharedCheck_2510_ == 0 {
                        v___x_2505_ = v___x_2483_;
                        v_isShared_2506_ = v_isSharedCheck_2510_;
                        state = 5;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_2503_);
                        leanh::lean_dec(v___x_2483_);
                        v___x_2505_ = leanh::lean_box(0);
                        v_isShared_2506_ = v_isSharedCheck_2510_;
                        state = 5;
                        continue;
                    }
                }
            }
            1 => {
                v_sysname_2488_ = leanh::lean_ctor_get(v_a_2484_, 0);
                v_release_2489_ = leanh::lean_ctor_get(v_a_2484_, 1);
                v_version_2490_ = leanh::lean_ctor_get(v_a_2484_, 2);
                v_machine_2491_ = leanh::lean_ctor_get(v_a_2484_, 3);
                v_isSharedCheck_2501_ = (!leanh::lean_is_exclusive(v_a_2484_)) as u8;
                if v_isSharedCheck_2501_ == 0 {
                    v___x_2493_ = v_a_2484_;
                    v_isShared_2494_ = v_isSharedCheck_2501_;
                    state = 2;
                    continue;
                } else {
                    leanh::lean_inc(v_machine_2491_);
                    leanh::lean_inc(v_version_2490_);
                    leanh::lean_inc(v_release_2489_);
                    leanh::lean_inc(v_sysname_2488_);
                    leanh::lean_dec(v_a_2484_);
                    v___x_2493_ = leanh::lean_box(0);
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
                    v_reuseFailAlloc_2500_ = leanh::lean_alloc_ctor(0, 4, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2500_, 0, v_sysname_2488_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2500_, 1, v_release_2489_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2500_, 2, v_version_2490_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2500_, 3, v_machine_2491_);
                    v___x_2496_ = v_reuseFailAlloc_2500_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_2487_ == 0 {
                    leanh::lean_ctor_set(v___x_2486_, 0, v___x_2496_);
                    v___x_2498_ = v___x_2486_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2499_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2499_, 0, v___x_2496_);
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
                    v_reuseFailAlloc_2509_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2509_, 0, v_a_2503_);
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
    mut v_a_2511_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2512_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2512_ = l_Std_Async_System_getSystemInfo();
    return v_res_2512_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_Async_System_getCPUInfo_spec__1_spec__1(
    mut v_sz_2513_: usize,
    mut v_i_2514_: usize,
    mut v_bs_2515_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2516_: u8 = 0;
    let mut v_v_2517_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_times_2518_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_model_2519_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_speed_2520_: u64 = 0;
    let mut v_user_2521_: u64 = 0;
    let mut v_nice_2522_: u64 = 0;
    let mut v_sys_2523_: u64 = 0;
    let mut v_idle_2524_: u64 = 0;
    let mut v_irq_2525_: u64 = 0;
    let mut v___x_2526_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_bs_x27_2527_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2528_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2529_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2530_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2531_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2532_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2533_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2534_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2535_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2536_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2537_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2538_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2539_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2540_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2541_: usize = 0;
    let mut v___x_2542_: usize = 0;
    let mut v___x_2543_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2516_ = lean_usize_dec_lt(v_i_2514_, v_sz_2513_);
                if v___x_2516_ == 0 {
                    return v_bs_2515_;
                } else {
                    v_v_2517_ = lean_array_uget_borrowed(v_bs_2515_, v_i_2514_);
                    v_times_2518_ = leanh::lean_ctor_get(v_v_2517_, 1);
                    v_model_2519_ = leanh::lean_ctor_get(v_v_2517_, 0);
                    leanh::lean_inc_ref(v_model_2519_);
                    v_speed_2520_ = leanh::lean_ctor_get_uint64(
                        v_v_2517_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 2) as u32,
                    );
                    v_user_2521_ = leanh::lean_ctor_get_uint64(v_times_2518_, 0 as u32);
                    v_nice_2522_ = leanh::lean_ctor_get_uint64(v_times_2518_, 8 as u32);
                    v_sys_2523_ = leanh::lean_ctor_get_uint64(v_times_2518_, 16 as u32);
                    v_idle_2524_ = leanh::lean_ctor_get_uint64(v_times_2518_, 24 as u32);
                    v_irq_2525_ = leanh::lean_ctor_get_uint64(v_times_2518_, 32 as u32);
                    v___x_2526_ = leanh::lean_unsigned_to_nat(0);
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
                    v___x_2539_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    leanh::lean_ctor_set(v___x_2539_, 0, v___x_2530_);
                    leanh::lean_ctor_set(v___x_2539_, 1, v___x_2532_);
                    leanh::lean_ctor_set(v___x_2539_, 2, v___x_2534_);
                    leanh::lean_ctor_set(v___x_2539_, 3, v___x_2536_);
                    leanh::lean_ctor_set(v___x_2539_, 4, v___x_2538_);
                    v___x_2540_ = leanh::lean_alloc_ctor(0, 3, (0) as u32);
                    leanh::lean_ctor_set(v___x_2540_, 0, v_model_2519_);
                    leanh::lean_ctor_set(v___x_2540_, 1, v___x_2528_);
                    leanh::lean_ctor_set(v___x_2540_, 2, v___x_2539_);
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
    mut v_sz_2545_: *mut leanh::LeanObject,
    mut v_i_2546_: *mut leanh::LeanObject,
    mut v_bs_2547_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_sz_boxed_2548_: usize = 0;
    let mut v_i_boxed_2549_: usize = 0;
    let mut v_res_2550_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_2548_ = leanh::lean_unbox_usize(v_sz_2545_);
    leanh::lean_dec(v_sz_2545_);
    v_i_boxed_2549_ = leanh::lean_unbox_usize(v_i_2546_);
    leanh::lean_dec(v_i_2546_);
    v_res_2550_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_Async_System_getCPUInfo_spec__1_spec__1(v_sz_boxed_2548_, v_i_boxed_2549_, v_bs_2547_);
    return v_res_2550_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_Async_System_getCPUInfo_spec__1(
    mut v_sz_2551_: usize,
    mut v_i_2552_: usize,
    mut v_bs_2553_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2554_: u8 = 0;
    v___x_2554_ = lean_usize_dec_lt(v_i_2552_, v_sz_2551_);
    if v___x_2554_ == 0 {
        return v_bs_2553_;
    } else {
        let mut v_v_2555_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_times_2556_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_model_2557_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_speed_2558_: u64 = 0;
        let mut v_user_2559_: u64 = 0;
        let mut v_nice_2560_: u64 = 0;
        let mut v_sys_2561_: u64 = 0;
        let mut v_idle_2562_: u64 = 0;
        let mut v_irq_2563_: u64 = 0;
        let mut v___x_2564_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_bs_x27_2565_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2566_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2567_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2568_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2569_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2570_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2571_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2572_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2573_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2574_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2575_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2576_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2577_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2578_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2579_: usize = 0;
        let mut v___x_2580_: usize = 0;
        let mut v___x_2581_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2582_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_v_2555_ = lean_array_uget_borrowed(v_bs_2553_, v_i_2552_);
        v_times_2556_ = leanh::lean_ctor_get(v_v_2555_, 1);
        v_model_2557_ = leanh::lean_ctor_get(v_v_2555_, 0);
        leanh::lean_inc_ref(v_model_2557_);
        v_speed_2558_ = leanh::lean_ctor_get_uint64(
            v_v_2555_,
            (core::mem::size_of::<*mut leanh::LeanObject>() * 2) as u32,
        );
        v_user_2559_ = leanh::lean_ctor_get_uint64(v_times_2556_, 0 as u32);
        v_nice_2560_ = leanh::lean_ctor_get_uint64(v_times_2556_, 8 as u32);
        v_sys_2561_ = leanh::lean_ctor_get_uint64(v_times_2556_, 16 as u32);
        v_idle_2562_ = leanh::lean_ctor_get_uint64(v_times_2556_, 24 as u32);
        v_irq_2563_ = leanh::lean_ctor_get_uint64(v_times_2556_, 32 as u32);
        v___x_2564_ = leanh::lean_unsigned_to_nat(0);
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
        v___x_2577_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
        leanh::lean_ctor_set(v___x_2577_, 0, v___x_2568_);
        leanh::lean_ctor_set(v___x_2577_, 1, v___x_2570_);
        leanh::lean_ctor_set(v___x_2577_, 2, v___x_2572_);
        leanh::lean_ctor_set(v___x_2577_, 3, v___x_2574_);
        leanh::lean_ctor_set(v___x_2577_, 4, v___x_2576_);
        v___x_2578_ = leanh::lean_alloc_ctor(0, 3, (0) as u32);
        leanh::lean_ctor_set(v___x_2578_, 0, v_model_2557_);
        leanh::lean_ctor_set(v___x_2578_, 1, v___x_2566_);
        leanh::lean_ctor_set(v___x_2578_, 2, v___x_2577_);
        v___x_2579_ = 1usize;
        v___x_2580_ = lean_usize_add(v_i_2552_, v___x_2579_);
        v___x_2581_ = lean_array_uset(v_bs_x27_2565_, v_i_2552_, v___x_2578_);
        v___x_2582_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_Async_System_getCPUInfo_spec__1_spec__1(v_sz_2551_, v___x_2580_, v___x_2581_);
        return v___x_2582_;
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_Async_System_getCPUInfo_spec__1___boxed(
    mut v_sz_2583_: *mut leanh::LeanObject,
    mut v_i_2584_: *mut leanh::LeanObject,
    mut v_bs_2585_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_sz_boxed_2586_: usize = 0;
    let mut v_i_boxed_2587_: usize = 0;
    let mut v_res_2588_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_2586_ = leanh::lean_unbox_usize(v_sz_2583_);
    leanh::lean_dec(v_sz_2583_);
    v_i_boxed_2587_ = leanh::lean_unbox_usize(v_i_2584_);
    leanh::lean_dec(v_i_2584_);
    v_res_2588_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_Async_System_getCPUInfo_spec__1(v_sz_boxed_2586_, v_i_boxed_2587_, v_bs_2585_);
    return v_res_2588_;
}
pub unsafe fn l_Std_Async_System_getCPUInfo() -> *mut leanh::LeanObject {
    let mut v___x_2590_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2591_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2593_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2594_: u8 = 0;
    let mut v_sz_2595_: usize = 0;
    let mut v___x_2596_: usize = 0;
    let mut v___x_2597_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2599_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2600_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2601_: u8 = 0;
    let mut v_a_2602_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2604_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2605_: u8 = 0;
    let mut v___x_2607_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2608_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2609_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2590_ = lean_uv_cpu_info();
                if leanh::lean_obj_tag(v___x_2590_) == 0 {
                    v_a_2591_ = leanh::lean_ctor_get(v___x_2590_, 0);
                    v_isSharedCheck_2601_ = (!leanh::lean_is_exclusive(v___x_2590_)) as u8;
                    if v_isSharedCheck_2601_ == 0 {
                        v___x_2593_ = v___x_2590_;
                        v_isShared_2594_ = v_isSharedCheck_2601_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_2591_);
                        leanh::lean_dec(v___x_2590_);
                        v___x_2593_ = leanh::lean_box(0);
                        v_isShared_2594_ = v_isSharedCheck_2601_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_2602_ = leanh::lean_ctor_get(v___x_2590_, 0);
                    v_isSharedCheck_2609_ = (!leanh::lean_is_exclusive(v___x_2590_)) as u8;
                    if v_isSharedCheck_2609_ == 0 {
                        v___x_2604_ = v___x_2590_;
                        v_isShared_2605_ = v_isSharedCheck_2609_;
                        state = 3;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_2602_);
                        leanh::lean_dec(v___x_2590_);
                        v___x_2604_ = leanh::lean_box(0);
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
                    leanh::lean_ctor_set(v___x_2593_, 0, v___x_2597_);
                    v___x_2599_ = v___x_2593_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2600_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2600_, 0, v___x_2597_);
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
                    v_reuseFailAlloc_2608_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2608_, 0, v_a_2602_);
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
    mut v_a_2610_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2611_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2611_ = l_Std_Async_System_getCPUInfo();
    return v_res_2611_;
}
pub unsafe fn l_Nat_cast___at___00Std_Async_System_getCPUInfo_spec__0(
    mut v_a_2612_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2613_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2614_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2613_ = lean_nat_to_int(v_a_2612_);
    v___x_2614_ = l_Rat_ofInt(v___x_2613_);
    return v___x_2614_;
}
pub unsafe fn l_Std_Async_System_getUpTime() -> *mut leanh::LeanObject {
    let mut v___x_2616_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2617_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2619_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2620_: u8 = 0;
    let mut v___x_2621_: u64 = 0;
    let mut v___x_2622_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2623_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2625_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2626_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2627_: u8 = 0;
    let mut v_a_2628_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2630_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2631_: u8 = 0;
    let mut v___x_2633_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2634_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2635_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2616_ = lean_uv_uptime();
                if leanh::lean_obj_tag(v___x_2616_) == 0 {
                    v_a_2617_ = leanh::lean_ctor_get(v___x_2616_, 0);
                    v_isSharedCheck_2627_ = (!leanh::lean_is_exclusive(v___x_2616_)) as u8;
                    if v_isSharedCheck_2627_ == 0 {
                        v___x_2619_ = v___x_2616_;
                        v_isShared_2620_ = v_isSharedCheck_2627_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_2617_);
                        leanh::lean_dec(v___x_2616_);
                        v___x_2619_ = leanh::lean_box(0);
                        v_isShared_2620_ = v_isSharedCheck_2627_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_2628_ = leanh::lean_ctor_get(v___x_2616_, 0);
                    v_isSharedCheck_2635_ = (!leanh::lean_is_exclusive(v___x_2616_)) as u8;
                    if v_isSharedCheck_2635_ == 0 {
                        v___x_2630_ = v___x_2616_;
                        v_isShared_2631_ = v_isSharedCheck_2635_;
                        state = 3;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_2628_);
                        leanh::lean_dec(v___x_2616_);
                        v___x_2630_ = leanh::lean_box(0);
                        v_isShared_2631_ = v_isSharedCheck_2635_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v___x_2621_ = leanh::lean_unbox_uint64(v_a_2617_);
                leanh::lean_dec(v_a_2617_);
                v___x_2622_ = lean_uint64_to_nat(v___x_2621_);
                v___x_2623_ = lean_nat_to_int(v___x_2622_);
                if v_isShared_2620_ == 0 {
                    leanh::lean_ctor_set(v___x_2619_, 0, v___x_2623_);
                    v___x_2625_ = v___x_2619_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2626_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2626_, 0, v___x_2623_);
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
                    v_reuseFailAlloc_2634_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2634_, 0, v_a_2628_);
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
    mut v_a_2636_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2637_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2637_ = l_Std_Async_System_getUpTime();
    return v_res_2637_;
}
pub unsafe fn l_Std_Async_System_getHighResolutionTime() -> *mut leanh::LeanObject {
    let mut v___x_2639_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2640_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2642_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2643_: u8 = 0;
    let mut v___x_2644_: u64 = 0;
    let mut v___x_2645_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2646_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2648_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2649_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2650_: u8 = 0;
    let mut v_a_2651_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2653_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2654_: u8 = 0;
    let mut v___x_2656_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2657_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2658_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2639_ = lean_uv_hrtime();
                if leanh::lean_obj_tag(v___x_2639_) == 0 {
                    v_a_2640_ = leanh::lean_ctor_get(v___x_2639_, 0);
                    v_isSharedCheck_2650_ = (!leanh::lean_is_exclusive(v___x_2639_)) as u8;
                    if v_isSharedCheck_2650_ == 0 {
                        v___x_2642_ = v___x_2639_;
                        v_isShared_2643_ = v_isSharedCheck_2650_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_2640_);
                        leanh::lean_dec(v___x_2639_);
                        v___x_2642_ = leanh::lean_box(0);
                        v_isShared_2643_ = v_isSharedCheck_2650_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_2651_ = leanh::lean_ctor_get(v___x_2639_, 0);
                    v_isSharedCheck_2658_ = (!leanh::lean_is_exclusive(v___x_2639_)) as u8;
                    if v_isSharedCheck_2658_ == 0 {
                        v___x_2653_ = v___x_2639_;
                        v_isShared_2654_ = v_isSharedCheck_2658_;
                        state = 3;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_2651_);
                        leanh::lean_dec(v___x_2639_);
                        v___x_2653_ = leanh::lean_box(0);
                        v_isShared_2654_ = v_isSharedCheck_2658_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v___x_2644_ = leanh::lean_unbox_uint64(v_a_2640_);
                leanh::lean_dec(v_a_2640_);
                v___x_2645_ = lean_uint64_to_nat(v___x_2644_);
                v___x_2646_ = lean_nat_to_int(v___x_2645_);
                if v_isShared_2643_ == 0 {
                    leanh::lean_ctor_set(v___x_2642_, 0, v___x_2646_);
                    v___x_2648_ = v___x_2642_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2649_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2649_, 0, v___x_2646_);
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
                    v_reuseFailAlloc_2657_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2657_, 0, v_a_2651_);
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
    mut v_a_2659_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2660_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2660_ = l_Std_Async_System_getHighResolutionTime();
    return v_res_2660_;
}
pub unsafe fn l_Std_Async_System_getHostName() -> *mut leanh::LeanObject {
    let mut v___x_2662_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2662_ = lean_uv_os_gethostname();
    return v___x_2662_;
}
pub unsafe fn l_Std_Async_System_getHostName___boxed(
    mut v_a_2663_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2664_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2664_ = l_Std_Async_System_getHostName();
    return v_res_2664_;
}
pub unsafe fn l_Std_Async_System_setEnvVar(
    mut v_name_2665_: *mut leanh::LeanObject,
    mut v_value_2666_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2668_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2668_ = lean_uv_os_setenv(v_name_2665_, v_value_2666_);
    return v___x_2668_;
}
pub unsafe fn l_Std_Async_System_setEnvVar___boxed(
    mut v_name_2669_: *mut leanh::LeanObject,
    mut v_value_2670_: *mut leanh::LeanObject,
    mut v_a_2671_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2672_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2672_ = l_Std_Async_System_setEnvVar(v_name_2669_, v_value_2670_);
    leanh::lean_dec_ref(v_value_2670_);
    leanh::lean_dec_ref(v_name_2669_);
    return v_res_2672_;
}
pub unsafe fn l_Std_Async_System_getEnvVar(
    mut v_name_2673_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2675_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2675_ = lean_uv_os_getenv(v_name_2673_);
    return v___x_2675_;
}
pub unsafe fn l_Std_Async_System_getEnvVar___boxed(
    mut v_name_2676_: *mut leanh::LeanObject,
    mut v_a_2677_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2678_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2678_ = l_Std_Async_System_getEnvVar(v_name_2676_);
    leanh::lean_dec_ref(v_name_2676_);
    return v_res_2678_;
}
pub unsafe fn l_Std_Async_System_unsetEnvVar(
    mut v_name_2679_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2681_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2681_ = lean_uv_os_unsetenv(v_name_2679_);
    return v___x_2681_;
}
pub unsafe fn l_Std_Async_System_unsetEnvVar___boxed(
    mut v_name_2682_: *mut leanh::LeanObject,
    mut v_a_2683_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2684_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2684_ = l_Std_Async_System_unsetEnvVar(v_name_2682_);
    leanh::lean_dec_ref(v_name_2682_);
    return v_res_2684_;
}
pub unsafe fn l_Std_Async_System_getEnv() -> *mut leanh::LeanObject {
    let mut v___x_2709_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2710_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2712_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2713_: u8 = 0;
    let mut v___x_2714_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2715_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2716_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2717_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2718_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2719_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2720_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2721_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2722_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2723_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2724_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2725_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2726_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2727_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2729_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2730_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2731_: u8 = 0;
    let mut v_a_2732_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2734_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2735_: u8 = 0;
    let mut v___x_2737_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2738_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2739_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2709_ = lean_uv_os_environ();
                if leanh::lean_obj_tag(v___x_2709_) == 0 {
                    v_a_2710_ = leanh::lean_ctor_get(v___x_2709_, 0);
                    v_isSharedCheck_2731_ = (!leanh::lean_is_exclusive(v___x_2709_)) as u8;
                    if v_isSharedCheck_2731_ == 0 {
                        v___x_2712_ = v___x_2709_;
                        v_isShared_2713_ = v_isSharedCheck_2731_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_2710_);
                        leanh::lean_dec(v___x_2709_);
                        v___x_2712_ = leanh::lean_box(0);
                        v_isShared_2713_ = v_isSharedCheck_2731_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_2732_ = leanh::lean_ctor_get(v___x_2709_, 0);
                    v_isSharedCheck_2739_ = (!leanh::lean_is_exclusive(v___x_2709_)) as u8;
                    if v_isSharedCheck_2739_ == 0 {
                        v___x_2734_ = v___x_2709_;
                        v_isShared_2735_ = v_isSharedCheck_2739_;
                        state = 3;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_2732_);
                        leanh::lean_dec(v___x_2709_);
                        v___x_2734_ = leanh::lean_box(0);
                        v_isShared_2735_ = v_isSharedCheck_2739_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v___x_2714_ = l_Std_Async_System_Environment_get_x3f___closed__0;
                v___f_2715_ = l_Std_Async_System_getEnv___closed__11;
                v___f_2716_ = leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Std_Async_System_Environment_get_x3f___closed__1),
                    core::ptr::addr_of_mut!(
                        l_Std_Async_System_Environment_get_x3f___closed__1_once
                    ),
                    _init_l_Std_Async_System_Environment_get_x3f___closed__1,
                );
                v___x_2717_ = lean_array_get_size(v_a_2710_);
                v___x_2718_ = leanh::lean_unsigned_to_nat(0);
                v___x_2719_ = leanh::lean_unsigned_to_nat(4);
                v___x_2720_ = lean_nat_mul(v___x_2717_, v___x_2719_);
                v___x_2721_ = leanh::lean_unsigned_to_nat(3);
                v___x_2722_ = lean_nat_div(v___x_2720_, v___x_2721_);
                leanh::lean_dec(v___x_2720_);
                v___x_2723_ = l_Nat_nextPowerOfTwo(v___x_2722_);
                leanh::lean_dec(v___x_2722_);
                v___x_2724_ = leanh::lean_box(0);
                v___x_2725_ = lean_mk_array(v___x_2723_, v___x_2724_);
                v___x_2726_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_2726_, 0, v___x_2718_);
                leanh::lean_ctor_set(v___x_2726_, 1, v___x_2725_);
                v___x_2727_ = l_Std_DHashMap_Internal_Raw_u2080_Const_insertMany___redArg(
                    v___f_2715_,
                    v___f_2716_,
                    v___x_2714_,
                    v___x_2726_,
                    v_a_2710_,
                );
                if v_isShared_2713_ == 0 {
                    leanh::lean_ctor_set(v___x_2712_, 0, v___x_2727_);
                    v___x_2729_ = v___x_2712_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2730_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2730_, 0, v___x_2727_);
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
                    v_reuseFailAlloc_2738_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2738_, 0, v_a_2732_);
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
    mut v_a_2740_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2741_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2741_ = l_Std_Async_System_getEnv();
    return v_res_2741_;
}
pub unsafe fn l_Std_Async_System_getHomeDir() -> *mut leanh::LeanObject {
    let mut v___x_2743_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2744_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2746_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2747_: u8 = 0;
    let mut v___x_2749_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2750_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2751_: u8 = 0;
    let mut v_a_2752_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2754_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2755_: u8 = 0;
    let mut v___x_2757_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2758_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2759_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2743_ = lean_uv_os_homedir();
                if leanh::lean_obj_tag(v___x_2743_) == 0 {
                    v_a_2744_ = leanh::lean_ctor_get(v___x_2743_, 0);
                    v_isSharedCheck_2751_ = (!leanh::lean_is_exclusive(v___x_2743_)) as u8;
                    if v_isSharedCheck_2751_ == 0 {
                        v___x_2746_ = v___x_2743_;
                        v_isShared_2747_ = v_isSharedCheck_2751_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_2744_);
                        leanh::lean_dec(v___x_2743_);
                        v___x_2746_ = leanh::lean_box(0);
                        v_isShared_2747_ = v_isSharedCheck_2751_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_2752_ = leanh::lean_ctor_get(v___x_2743_, 0);
                    v_isSharedCheck_2759_ = (!leanh::lean_is_exclusive(v___x_2743_)) as u8;
                    if v_isSharedCheck_2759_ == 0 {
                        v___x_2754_ = v___x_2743_;
                        v_isShared_2755_ = v_isSharedCheck_2759_;
                        state = 3;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_2752_);
                        leanh::lean_dec(v___x_2743_);
                        v___x_2754_ = leanh::lean_box(0);
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
                    v_reuseFailAlloc_2750_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2750_, 0, v_a_2744_);
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
                    v_reuseFailAlloc_2758_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2758_, 0, v_a_2752_);
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
    mut v_a_2760_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2761_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2761_ = l_Std_Async_System_getHomeDir();
    return v_res_2761_;
}
pub unsafe fn l_Std_Async_System_getTmpDir() -> *mut leanh::LeanObject {
    let mut v___x_2763_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2764_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2766_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2767_: u8 = 0;
    let mut v___x_2769_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2770_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2771_: u8 = 0;
    let mut v_a_2772_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2774_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2775_: u8 = 0;
    let mut v___x_2777_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2778_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2779_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2763_ = lean_uv_os_tmpdir();
                if leanh::lean_obj_tag(v___x_2763_) == 0 {
                    v_a_2764_ = leanh::lean_ctor_get(v___x_2763_, 0);
                    v_isSharedCheck_2771_ = (!leanh::lean_is_exclusive(v___x_2763_)) as u8;
                    if v_isSharedCheck_2771_ == 0 {
                        v___x_2766_ = v___x_2763_;
                        v_isShared_2767_ = v_isSharedCheck_2771_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_2764_);
                        leanh::lean_dec(v___x_2763_);
                        v___x_2766_ = leanh::lean_box(0);
                        v_isShared_2767_ = v_isSharedCheck_2771_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_2772_ = leanh::lean_ctor_get(v___x_2763_, 0);
                    v_isSharedCheck_2779_ = (!leanh::lean_is_exclusive(v___x_2763_)) as u8;
                    if v_isSharedCheck_2779_ == 0 {
                        v___x_2774_ = v___x_2763_;
                        v_isShared_2775_ = v_isSharedCheck_2779_;
                        state = 3;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_2772_);
                        leanh::lean_dec(v___x_2763_);
                        v___x_2774_ = leanh::lean_box(0);
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
                    v_reuseFailAlloc_2770_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2770_, 0, v_a_2764_);
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
                    v_reuseFailAlloc_2778_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2778_, 0, v_a_2772_);
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
    mut v_a_2780_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2781_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2781_ = l_Std_Async_System_getTmpDir();
    return v_res_2781_;
}
pub unsafe fn l_Std_Async_System_getCurrentUser() -> *mut leanh::LeanObject {
    let mut v___x_2783_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2784_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2786_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2787_: u8 = 0;
    let mut v_username_2788_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_uid_2789_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_gid_2790_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_shell_2791_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_homedir_2792_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2794_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2795_: u8 = 0;
    let mut v___y_2797_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2798_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2799_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2801_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2803_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2804_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2805_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2807_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2808_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2809_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2810_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2812_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2813_: u8 = 0;
    let mut v___x_2815_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2816_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2817_: u8 = 0;
    let mut v___y_2819_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2820_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2821_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2823_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2824_: u8 = 0;
    let mut v___x_2825_: u64 = 0;
    let mut v___x_2826_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2828_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2829_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2830_: u8 = 0;
    let mut v___x_2831_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2832_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2834_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2835_: u8 = 0;
    let mut v___x_2836_: u64 = 0;
    let mut v___x_2837_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2839_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2840_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2841_: u8 = 0;
    let mut v_isSharedCheck_2842_: u8 = 0;
    let mut v_isSharedCheck_2843_: u8 = 0;
    let mut v_a_2844_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2846_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2847_: u8 = 0;
    let mut v___x_2849_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2850_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2851_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2783_ = lean_uv_os_get_passwd();
                if leanh::lean_obj_tag(v___x_2783_) == 0 {
                    v_a_2784_ = leanh::lean_ctor_get(v___x_2783_, 0);
                    v_isSharedCheck_2843_ = (!leanh::lean_is_exclusive(v___x_2783_)) as u8;
                    if v_isSharedCheck_2843_ == 0 {
                        v___x_2786_ = v___x_2783_;
                        v_isShared_2787_ = v_isSharedCheck_2843_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_2784_);
                        leanh::lean_dec(v___x_2783_);
                        v___x_2786_ = leanh::lean_box(0);
                        v_isShared_2787_ = v_isSharedCheck_2843_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_2844_ = leanh::lean_ctor_get(v___x_2783_, 0);
                    v_isSharedCheck_2851_ = (!leanh::lean_is_exclusive(v___x_2783_)) as u8;
                    if v_isSharedCheck_2851_ == 0 {
                        v___x_2846_ = v___x_2783_;
                        v_isShared_2847_ = v_isSharedCheck_2851_;
                        state = 14;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_2844_);
                        leanh::lean_dec(v___x_2783_);
                        v___x_2846_ = leanh::lean_box(0);
                        v_isShared_2847_ = v_isSharedCheck_2851_;
                        state = 14;
                        continue;
                    }
                }
            }
            1 => {
                v_username_2788_ = leanh::lean_ctor_get(v_a_2784_, 0);
                v_uid_2789_ = leanh::lean_ctor_get(v_a_2784_, 1);
                v_gid_2790_ = leanh::lean_ctor_get(v_a_2784_, 2);
                v_shell_2791_ = leanh::lean_ctor_get(v_a_2784_, 3);
                v_homedir_2792_ = leanh::lean_ctor_get(v_a_2784_, 4);
                v_isSharedCheck_2842_ = (!leanh::lean_is_exclusive(v_a_2784_)) as u8;
                if v_isSharedCheck_2842_ == 0 {
                    v___x_2794_ = v_a_2784_;
                    v_isShared_2795_ = v_isSharedCheck_2842_;
                    state = 2;
                    continue;
                } else {
                    leanh::lean_inc(v_homedir_2792_);
                    leanh::lean_inc(v_shell_2791_);
                    leanh::lean_inc(v_gid_2790_);
                    leanh::lean_inc(v_uid_2789_);
                    leanh::lean_inc(v_username_2788_);
                    leanh::lean_dec(v_a_2784_);
                    v___x_2794_ = leanh::lean_box(0);
                    v_isShared_2795_ = v_isSharedCheck_2842_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                if leanh::lean_obj_tag(v_uid_2789_) == 0 {
                    v___x_2831_ = leanh::lean_box(0);
                    v___y_2819_ = v___x_2831_;
                    state = 9;
                    continue;
                } else {
                    v_val_2832_ = leanh::lean_ctor_get(v_uid_2789_, 0);
                    v_isSharedCheck_2841_ = (!leanh::lean_is_exclusive(v_uid_2789_)) as u8;
                    if v_isSharedCheck_2841_ == 0 {
                        v___x_2834_ = v_uid_2789_;
                        v_isShared_2835_ = v_isSharedCheck_2841_;
                        state = 12;
                        continue;
                    } else {
                        leanh::lean_inc(v_val_2832_);
                        leanh::lean_dec(v_uid_2789_);
                        v___x_2834_ = leanh::lean_box(0);
                        v_isShared_2835_ = v_isSharedCheck_2841_;
                        state = 12;
                        continue;
                    }
                }
            }
            3 => {
                if v_isShared_2795_ == 0 {
                    leanh::lean_ctor_set(v___x_2794_, 4, v___y_2799_);
                    leanh::lean_ctor_set(v___x_2794_, 2, v___y_2798_);
                    leanh::lean_ctor_set(v___x_2794_, 1, v___y_2797_);
                    v___x_2801_ = v___x_2794_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2805_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2805_, 0, v_username_2788_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2805_, 1, v___y_2797_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2805_, 2, v___y_2798_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2805_, 3, v_shell_2791_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2805_, 4, v___y_2799_);
                    v___x_2801_ = v_reuseFailAlloc_2805_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                if v_isShared_2787_ == 0 {
                    leanh::lean_ctor_set(v___x_2786_, 0, v___x_2801_);
                    v___x_2803_ = v___x_2786_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_2804_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2804_, 0, v___x_2801_);
                    v___x_2803_ = v_reuseFailAlloc_2804_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_2803_;
            }
            6 => {
                if leanh::lean_obj_tag(v_homedir_2792_) == 0 {
                    v___x_2809_ = leanh::lean_box(0);
                    v___y_2797_ = v___y_2807_;
                    v___y_2798_ = v___y_2808_;
                    v___y_2799_ = v___x_2809_;
                    state = 3;
                    continue;
                } else {
                    v_val_2810_ = leanh::lean_ctor_get(v_homedir_2792_, 0);
                    v_isSharedCheck_2817_ =
                        (!leanh::lean_is_exclusive(v_homedir_2792_)) as u8;
                    if v_isSharedCheck_2817_ == 0 {
                        v___x_2812_ = v_homedir_2792_;
                        v_isShared_2813_ = v_isSharedCheck_2817_;
                        state = 7;
                        continue;
                    } else {
                        leanh::lean_inc(v_val_2810_);
                        leanh::lean_dec(v_homedir_2792_);
                        v___x_2812_ = leanh::lean_box(0);
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
                    v_reuseFailAlloc_2816_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2816_, 0, v_val_2810_);
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
                if leanh::lean_obj_tag(v_gid_2790_) == 0 {
                    v___x_2820_ = leanh::lean_box(0);
                    v___y_2807_ = v___y_2819_;
                    v___y_2808_ = v___x_2820_;
                    state = 6;
                    continue;
                } else {
                    v_val_2821_ = leanh::lean_ctor_get(v_gid_2790_, 0);
                    v_isSharedCheck_2830_ = (!leanh::lean_is_exclusive(v_gid_2790_)) as u8;
                    if v_isSharedCheck_2830_ == 0 {
                        v___x_2823_ = v_gid_2790_;
                        v_isShared_2824_ = v_isSharedCheck_2830_;
                        state = 10;
                        continue;
                    } else {
                        leanh::lean_inc(v_val_2821_);
                        leanh::lean_dec(v_gid_2790_);
                        v___x_2823_ = leanh::lean_box(0);
                        v_isShared_2824_ = v_isSharedCheck_2830_;
                        state = 10;
                        continue;
                    }
                }
            }
            10 => {
                v___x_2825_ = leanh::lean_unbox_uint64(v_val_2821_);
                leanh::lean_dec(v_val_2821_);
                v___x_2826_ = lean_uint64_to_nat(v___x_2825_);
                if v_isShared_2824_ == 0 {
                    leanh::lean_ctor_set(v___x_2823_, 0, v___x_2826_);
                    v___x_2828_ = v___x_2823_;
                    state = 11;
                    continue;
                } else {
                    v_reuseFailAlloc_2829_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2829_, 0, v___x_2826_);
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
                v___x_2836_ = leanh::lean_unbox_uint64(v_val_2832_);
                leanh::lean_dec(v_val_2832_);
                v___x_2837_ = lean_uint64_to_nat(v___x_2836_);
                if v_isShared_2835_ == 0 {
                    leanh::lean_ctor_set(v___x_2834_, 0, v___x_2837_);
                    v___x_2839_ = v___x_2834_;
                    state = 13;
                    continue;
                } else {
                    v_reuseFailAlloc_2840_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2840_, 0, v___x_2837_);
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
                    v_reuseFailAlloc_2850_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2850_, 0, v_a_2844_);
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
    mut v_a_2852_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2853_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2853_ = l_Std_Async_System_getCurrentUser();
    return v_res_2853_;
}
pub unsafe fn l_Functor_mapRev___at___00Std_Async_System_getGroup_spec__0___redArg(
    mut v_a_2854_: *mut leanh::LeanObject,
    mut v_f_2855_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2856_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2857_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2859_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2860_: u8 = 0;
    let mut v___x_2861_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2863_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2864_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2865_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_a_2854_) == 0 {
                    leanh::lean_dec(v_f_2855_);
                    v___x_2856_ = leanh::lean_box(0);
                    return v___x_2856_;
                } else {
                    v_val_2857_ = leanh::lean_ctor_get(v_a_2854_, 0);
                    v_isSharedCheck_2865_ = (!leanh::lean_is_exclusive(v_a_2854_)) as u8;
                    if v_isSharedCheck_2865_ == 0 {
                        v___x_2859_ = v_a_2854_;
                        v_isShared_2860_ = v_isSharedCheck_2865_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_val_2857_);
                        leanh::lean_dec(v_a_2854_);
                        v___x_2859_ = leanh::lean_box(0);
                        v_isShared_2860_ = v_isSharedCheck_2865_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_2861_ = leanh::lean_apply_1(v_f_2855_, v_val_2857_);
                if v_isShared_2860_ == 0 {
                    leanh::lean_ctor_set(v___x_2859_, 0, v___x_2861_);
                    v___x_2863_ = v___x_2859_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2864_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2864_, 0, v___x_2861_);
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
    mut v_00_u03b1_2866_: *mut leanh::LeanObject,
    mut v_00_u03b2_2867_: *mut leanh::LeanObject,
    mut v_a_2868_: *mut leanh::LeanObject,
    mut v_f_2869_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2870_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2870_ =
        l_Functor_mapRev___at___00Std_Async_System_getGroup_spec__0___redArg(v_a_2868_, v_f_2869_);
    return v___x_2870_;
}
pub unsafe fn l_Std_Async_System_getGroup___lam__0(
    mut v_group_2871_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_groupname_2872_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_gid_2873_: u64 = 0;
    let mut v_members_2874_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2875_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2876_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_groupname_2872_ = leanh::lean_ctor_get(v_group_2871_, 0);
    v_gid_2873_ = leanh::lean_ctor_get_uint64(
        v_group_2871_,
        (core::mem::size_of::<*mut leanh::LeanObject>() * 2) as u32,
    );
    v_members_2874_ = leanh::lean_ctor_get(v_group_2871_, 1);
    v___x_2875_ = lean_uint64_to_nat(v_gid_2873_);
    leanh::lean_inc_ref(v_members_2874_);
    leanh::lean_inc_ref(v_groupname_2872_);
    v___x_2876_ = leanh::lean_alloc_ctor(0, 3, (0) as u32);
    leanh::lean_ctor_set(v___x_2876_, 0, v_groupname_2872_);
    leanh::lean_ctor_set(v___x_2876_, 1, v___x_2875_);
    leanh::lean_ctor_set(v___x_2876_, 2, v_members_2874_);
    return v___x_2876_;
}
pub unsafe fn l_Std_Async_System_getGroup___lam__0___boxed(
    mut v_group_2877_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2878_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2878_ = l_Std_Async_System_getGroup___lam__0(v_group_2877_);
    leanh::lean_dec_ref(v_group_2877_);
    return v_res_2878_;
}
pub unsafe fn l_Std_Async_System_getGroup(
    mut v_groupId_2880_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2882_: u64 = 0;
    let mut v___x_2883_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2884_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2886_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2887_: u8 = 0;
    let mut v___f_2888_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2889_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2891_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2892_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2893_: u8 = 0;
    let mut v_a_2894_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2896_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2897_: u8 = 0;
    let mut v___x_2899_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2900_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2901_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2882_ = lean_uint64_of_nat(v_groupId_2880_);
                v___x_2883_ = lean_uv_os_get_group(v___x_2882_);
                if leanh::lean_obj_tag(v___x_2883_) == 0 {
                    v_a_2884_ = leanh::lean_ctor_get(v___x_2883_, 0);
                    v_isSharedCheck_2893_ = (!leanh::lean_is_exclusive(v___x_2883_)) as u8;
                    if v_isSharedCheck_2893_ == 0 {
                        v___x_2886_ = v___x_2883_;
                        v_isShared_2887_ = v_isSharedCheck_2893_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_2884_);
                        leanh::lean_dec(v___x_2883_);
                        v___x_2886_ = leanh::lean_box(0);
                        v_isShared_2887_ = v_isSharedCheck_2893_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_2894_ = leanh::lean_ctor_get(v___x_2883_, 0);
                    v_isSharedCheck_2901_ = (!leanh::lean_is_exclusive(v___x_2883_)) as u8;
                    if v_isSharedCheck_2901_ == 0 {
                        v___x_2896_ = v___x_2883_;
                        v_isShared_2897_ = v_isSharedCheck_2901_;
                        state = 3;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_2894_);
                        leanh::lean_dec(v___x_2883_);
                        v___x_2896_ = leanh::lean_box(0);
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
                    leanh::lean_ctor_set(v___x_2886_, 0, v___x_2889_);
                    v___x_2891_ = v___x_2886_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2892_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2892_, 0, v___x_2889_);
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
                    v_reuseFailAlloc_2900_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2900_, 0, v_a_2894_);
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
    mut v_groupId_2902_: *mut leanh::LeanObject,
    mut v_a_2903_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2904_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2904_ = l_Std_Async_System_getGroup(v_groupId_2902_);
    leanh::lean_dec(v_groupId_2902_);
    return v_res_2904_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Std_Async_System(builtin: u8) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Std_Time(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Std_Internal_UV_System(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Std_Data_HashMap(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    l_Std_Async_System_instInhabitedGroupId_default =
        _init_l_Std_Async_System_instInhabitedGroupId_default();
    leanh::lean_mark_persistent(l_Std_Async_System_instInhabitedGroupId_default);
    l_Std_Async_System_instInhabitedGroupId = _init_l_Std_Async_System_instInhabitedGroupId();
    leanh::lean_mark_persistent(l_Std_Async_System_instInhabitedGroupId);
    l_Std_Async_System_instInhabitedUserId_default =
        _init_l_Std_Async_System_instInhabitedUserId_default();
    leanh::lean_mark_persistent(l_Std_Async_System_instInhabitedUserId_default);
    l_Std_Async_System_instInhabitedUserId = _init_l_Std_Async_System_instInhabitedUserId();
    leanh::lean_mark_persistent(l_Std_Async_System_instInhabitedUserId);
    l_Std_Async_System_instInhabitedCPUTimes_default =
        _init_l_Std_Async_System_instInhabitedCPUTimes_default();
    leanh::lean_mark_persistent(l_Std_Async_System_instInhabitedCPUTimes_default);
    l_Std_Async_System_instInhabitedCPUTimes = _init_l_Std_Async_System_instInhabitedCPUTimes();
    leanh::lean_mark_persistent(l_Std_Async_System_instInhabitedCPUTimes);
    l_Std_Async_System_instInhabitedCPUInfo_default =
        _init_l_Std_Async_System_instInhabitedCPUInfo_default();
    leanh::lean_mark_persistent(l_Std_Async_System_instInhabitedCPUInfo_default);
    l_Std_Async_System_instInhabitedCPUInfo = _init_l_Std_Async_System_instInhabitedCPUInfo();
    leanh::lean_mark_persistent(l_Std_Async_System_instInhabitedCPUInfo);
    l_Std_Async_System_instInhabitedEnvironment_default =
        _init_l_Std_Async_System_instInhabitedEnvironment_default();
    leanh::lean_mark_persistent(l_Std_Async_System_instInhabitedEnvironment_default);
    l_Std_Async_System_instInhabitedEnvironment =
        _init_l_Std_Async_System_instInhabitedEnvironment();
    leanh::lean_mark_persistent(l_Std_Async_System_instInhabitedEnvironment);
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Std_Async_System(builtin: u8) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_meta_initialized = true;
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Std_Async_System(builtin: u8) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Std_Time(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Std_Internal_UV_System(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Std_Data_HashMap(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Std_Async_System(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = meta_initialize_Std_Async_System(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return initialize_Std_Async_System(builtin);
}