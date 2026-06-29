// Lean compiler output
// Module: Lean.ProjFns
// Imports: Lean.EnvExtension
use crate::ffi::{
    lean_array_get_size, lean_array_push, lean_array_uget_borrowed, lean_nat_dec_le,
    lean_nat_dec_lt, lean_nat_to_int, lean_string_length, lean_usize_add, lean_usize_dec_eq,
    lean_usize_of_nat,
};
use crate::r#gen::Init::Data::Repr::{l_Bool_repr___redArg, l_Nat_reprFast};
use crate::r#gen::Init::Meta::Defs::l_Lean_Name_reprPrec;
use crate::r#gen::Lean::EnvExtension::{
    initialize_Lean_EnvExtension, l_Lean_MapDeclarationExtension_contains___redArg,
    l_Lean_MapDeclarationExtension_find_x3f___redArg,
    l_Lean_MapDeclarationExtension_insert___redArg, l_Lean_mkMapDeclarationExtension___redArg,
    runtime_initialize_Lean_EnvExtension,
};
use crate::r#gen::Lean::Environment::{l_Lean_Environment_contains, l_Lean_Environment_find_x3f};
pub static l_Lean_instInhabitedProjectionFunctionInfo_default___closed__0_value:
    crate::leanh::LeanCtorObject<4> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3
            + 8) as u16,
        other: 3,
        tag: 0,
    },
    m_objs: [
        (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
        (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
        (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
        0 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_instInhabitedProjectionFunctionInfo_default___closed__0:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_instInhabitedProjectionFunctionInfo_default___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Lean_instInhabitedProjectionFunctionInfo_default: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_instInhabitedProjectionFunctionInfo_default___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Lean_instInhabitedProjectionFunctionInfo: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_instInhabitedProjectionFunctionInfo_default___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_instReprProjectionFunctionInfo_repr___redArg___closed__0_value:
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
static mut l_Lean_instReprProjectionFunctionInfo_repr___redArg___closed__0:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_instReprProjectionFunctionInfo_repr___redArg___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_instReprProjectionFunctionInfo_repr___redArg___closed__1_value:
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
    m_data: [99, 116, 111, 114, 78, 97, 109, 101, 0],
};
static mut l_Lean_instReprProjectionFunctionInfo_repr___redArg___closed__1:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_instReprProjectionFunctionInfo_repr___redArg___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_instReprProjectionFunctionInfo_repr___redArg___closed__2_value:
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
        l_Lean_instReprProjectionFunctionInfo_repr___redArg___closed__1_value
    ) as *mut crate::leanh::LeanObject],
};
static mut l_Lean_instReprProjectionFunctionInfo_repr___redArg___closed__2:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_instReprProjectionFunctionInfo_repr___redArg___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_instReprProjectionFunctionInfo_repr___redArg___closed__3_value:
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
        core::ptr::addr_of!(l_Lean_instReprProjectionFunctionInfo_repr___redArg___closed__2_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_instReprProjectionFunctionInfo_repr___redArg___closed__3:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_instReprProjectionFunctionInfo_repr___redArg___closed__3_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_instReprProjectionFunctionInfo_repr___redArg___closed__4_value:
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
static mut l_Lean_instReprProjectionFunctionInfo_repr___redArg___closed__4:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_instReprProjectionFunctionInfo_repr___redArg___closed__4_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_instReprProjectionFunctionInfo_repr___redArg___closed__5_value:
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
        l_Lean_instReprProjectionFunctionInfo_repr___redArg___closed__4_value
    ) as *mut crate::leanh::LeanObject],
};
static mut l_Lean_instReprProjectionFunctionInfo_repr___redArg___closed__5:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_instReprProjectionFunctionInfo_repr___redArg___closed__5_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_instReprProjectionFunctionInfo_repr___redArg___closed__6_value:
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
        core::ptr::addr_of!(l_Lean_instReprProjectionFunctionInfo_repr___redArg___closed__3_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_instReprProjectionFunctionInfo_repr___redArg___closed__5_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_instReprProjectionFunctionInfo_repr___redArg___closed__6:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_instReprProjectionFunctionInfo_repr___redArg___closed__6_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_instReprProjectionFunctionInfo_repr___redArg___closed__7_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_instReprProjectionFunctionInfo_repr___redArg___closed__7:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_instReprProjectionFunctionInfo_repr___redArg___closed__8_value:
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
static mut l_Lean_instReprProjectionFunctionInfo_repr___redArg___closed__8:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_instReprProjectionFunctionInfo_repr___redArg___closed__8_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_instReprProjectionFunctionInfo_repr___redArg___closed__9_value:
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
        l_Lean_instReprProjectionFunctionInfo_repr___redArg___closed__8_value
    ) as *mut crate::leanh::LeanObject],
};
static mut l_Lean_instReprProjectionFunctionInfo_repr___redArg___closed__9:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_instReprProjectionFunctionInfo_repr___redArg___closed__9_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_instReprProjectionFunctionInfo_repr___redArg___closed__10_value:
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
    m_data: [110, 117, 109, 80, 97, 114, 97, 109, 115, 0],
};
static mut l_Lean_instReprProjectionFunctionInfo_repr___redArg___closed__10:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_instReprProjectionFunctionInfo_repr___redArg___closed__10_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_instReprProjectionFunctionInfo_repr___redArg___closed__11_value:
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
        l_Lean_instReprProjectionFunctionInfo_repr___redArg___closed__10_value
    ) as *mut crate::leanh::LeanObject],
};
static mut l_Lean_instReprProjectionFunctionInfo_repr___redArg___closed__11:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_instReprProjectionFunctionInfo_repr___redArg___closed__11_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_instReprProjectionFunctionInfo_repr___redArg___closed__12_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_instReprProjectionFunctionInfo_repr___redArg___closed__12:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_instReprProjectionFunctionInfo_repr___redArg___closed__13_value:
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
    m_data: [105, 0],
};
static mut l_Lean_instReprProjectionFunctionInfo_repr___redArg___closed__13:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_instReprProjectionFunctionInfo_repr___redArg___closed__13_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_instReprProjectionFunctionInfo_repr___redArg___closed__14_value:
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
        l_Lean_instReprProjectionFunctionInfo_repr___redArg___closed__13_value
    ) as *mut crate::leanh::LeanObject],
};
static mut l_Lean_instReprProjectionFunctionInfo_repr___redArg___closed__14:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_instReprProjectionFunctionInfo_repr___redArg___closed__14_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_instReprProjectionFunctionInfo_repr___redArg___closed__15_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_instReprProjectionFunctionInfo_repr___redArg___closed__15:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_instReprProjectionFunctionInfo_repr___redArg___closed__16_value:
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
    m_data: [102, 114, 111, 109, 67, 108, 97, 115, 115, 0],
};
static mut l_Lean_instReprProjectionFunctionInfo_repr___redArg___closed__16:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_instReprProjectionFunctionInfo_repr___redArg___closed__16_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_instReprProjectionFunctionInfo_repr___redArg___closed__17_value:
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
        l_Lean_instReprProjectionFunctionInfo_repr___redArg___closed__16_value
    ) as *mut crate::leanh::LeanObject],
};
static mut l_Lean_instReprProjectionFunctionInfo_repr___redArg___closed__17:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_instReprProjectionFunctionInfo_repr___redArg___closed__17_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_instReprProjectionFunctionInfo_repr___redArg___closed__18_value:
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
static mut l_Lean_instReprProjectionFunctionInfo_repr___redArg___closed__18:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_instReprProjectionFunctionInfo_repr___redArg___closed__18_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_instReprProjectionFunctionInfo_repr___redArg___closed__19_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_instReprProjectionFunctionInfo_repr___redArg___closed__19:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_instReprProjectionFunctionInfo_repr___redArg___closed__20_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_instReprProjectionFunctionInfo_repr___redArg___closed__20:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_instReprProjectionFunctionInfo_repr___redArg___closed__21_value:
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
        l_Lean_instReprProjectionFunctionInfo_repr___redArg___closed__0_value
    ) as *mut crate::leanh::LeanObject],
};
static mut l_Lean_instReprProjectionFunctionInfo_repr___redArg___closed__21:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_instReprProjectionFunctionInfo_repr___redArg___closed__21_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_instReprProjectionFunctionInfo_repr___redArg___closed__22_value:
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
        l_Lean_instReprProjectionFunctionInfo_repr___redArg___closed__18_value
    ) as *mut crate::leanh::LeanObject],
};
static mut l_Lean_instReprProjectionFunctionInfo_repr___redArg___closed__22:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_instReprProjectionFunctionInfo_repr___redArg___closed__22_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_instReprProjectionFunctionInfo___closed__0_value:
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
    m_fun: l_Lean_instReprProjectionFunctionInfo_repr___boxed as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_instReprProjectionFunctionInfo___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_instReprProjectionFunctionInfo___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Lean_instReprProjectionFunctionInfo: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_instReprProjectionFunctionInfo___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l___private_Lean_ProjFns_0__Lean_initFn___lam__0___closed__0_00___x40_Lean_ProjFns_2268652983____hygCtx___hyg_2__value: crate::leanh::LeanArrayObject<0> = crate::leanh::LeanArrayObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<usize>()*2 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 246 }, m_size: 0, m_capacity: 0, m_data: [] };
static mut l___private_Lean_ProjFns_0__Lean_initFn___lam__0___closed__0_00___x40_Lean_ProjFns_2268652983____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_ProjFns_0__Lean_initFn___lam__0___closed__0_00___x40_Lean_ProjFns_2268652983____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_ProjFns_0__Lean_initFn___lam__0___closed__1_00___x40_Lean_ProjFns_2268652983____hygCtx___hyg_2__value: crate::leanh::LeanArrayObject<0> = crate::leanh::LeanArrayObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<usize>()*2 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 246 }, m_size: 0, m_capacity: 0, m_data: [] };
static mut l___private_Lean_ProjFns_0__Lean_initFn___lam__0___closed__1_00___x40_Lean_ProjFns_2268652983____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_ProjFns_0__Lean_initFn___lam__0___closed__1_00___x40_Lean_ProjFns_2268652983____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_ProjFns_0__Lean_initFn___lam__0___closed__2_00___x40_Lean_ProjFns_2268652983____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*3 + 0) as u16, other: 3, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Lean_ProjFns_0__Lean_initFn___lam__0___closed__1_00___x40_Lean_ProjFns_2268652983____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_ProjFns_0__Lean_initFn___lam__0___closed__1_00___x40_Lean_ProjFns_2268652983____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_ProjFns_0__Lean_initFn___lam__0___closed__1_00___x40_Lean_ProjFns_2268652983____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_ProjFns_0__Lean_initFn___lam__0___closed__2_00___x40_Lean_ProjFns_2268652983____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_ProjFns_0__Lean_initFn___lam__0___closed__2_00___x40_Lean_ProjFns_2268652983____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_ProjFns_0__Lean_initFn___closed__0_00___x40_Lean_ProjFns_2268652983____hygCtx___hyg_2__value: crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l___private_Lean_ProjFns_0__Lean_initFn___lam__0_00___x40_Lean_ProjFns_2268652983____hygCtx___hyg_2____boxed as *const core::ffi::c_void, m_arity: 2, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_ProjFns_0__Lean_initFn___closed__0_00___x40_Lean_ProjFns_2268652983____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_ProjFns_0__Lean_initFn___closed__0_00___x40_Lean_ProjFns_2268652983____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_ProjFns_0__Lean_initFn___closed__1_00___x40_Lean_ProjFns_2268652983____hygCtx___hyg_2__value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [76, 101, 97, 110, 0]};
static mut l___private_Lean_ProjFns_0__Lean_initFn___closed__1_00___x40_Lean_ProjFns_2268652983____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_ProjFns_0__Lean_initFn___closed__1_00___x40_Lean_ProjFns_2268652983____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_ProjFns_0__Lean_initFn___closed__2_00___x40_Lean_ProjFns_2268652983____hygCtx___hyg_2__value: crate::leanh::LeanStringObject<20> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 20, m_capacity: 20, m_length: 19, m_data: [112, 114, 111, 106, 101, 99, 116, 105, 111, 110, 70, 110, 73, 110, 102, 111, 69, 120, 116, 0]};
static mut l___private_Lean_ProjFns_0__Lean_initFn___closed__2_00___x40_Lean_ProjFns_2268652983____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_ProjFns_0__Lean_initFn___closed__2_00___x40_Lean_ProjFns_2268652983____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
static l___private_Lean_ProjFns_0__Lean_initFn___closed__3_00___x40_Lean_ProjFns_2268652983____hygCtx___hyg_2__value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_ProjFns_0__Lean_initFn___closed__1_00___x40_Lean_ProjFns_2268652983____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_ProjFns_0__Lean_initFn___closed__3_00___x40_Lean_ProjFns_2268652983____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_ProjFns_0__Lean_initFn___closed__3_00___x40_Lean_ProjFns_2268652983____hygCtx___hyg_2__value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_ProjFns_0__Lean_initFn___closed__2_00___x40_Lean_ProjFns_2268652983____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,5140131695607655440 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_ProjFns_0__Lean_initFn___closed__3_00___x40_Lean_ProjFns_2268652983____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_ProjFns_0__Lean_initFn___closed__3_00___x40_Lean_ProjFns_2268652983____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_ProjFns_0__Lean_initFn___closed__4_00___x40_Lean_ProjFns_2268652983____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0 + 8) as u16, other: 0, tag: 3 }, m_objs: [0 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_ProjFns_0__Lean_initFn___closed__4_00___x40_Lean_ProjFns_2268652983____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_ProjFns_0__Lean_initFn___closed__4_00___x40_Lean_ProjFns_2268652983____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static mut l_Lean_projectionFnInfoExt: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_instInhabitedAuxParentProjectionInfo_default___closed__0_value:
    crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
            + 8) as u16,
        other: 1,
        tag: 0,
    },
    m_objs: [
        (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
        0 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_instInhabitedAuxParentProjectionInfo_default___closed__0:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_instInhabitedAuxParentProjectionInfo_default___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Lean_instInhabitedAuxParentProjectionInfo_default: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_instInhabitedAuxParentProjectionInfo_default___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Lean_instInhabitedAuxParentProjectionInfo: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_instInhabitedAuxParentProjectionInfo_default___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_instReprAuxParentProjectionInfo_repr___redArg___closed__0_value:
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
        core::ptr::addr_of!(l_Lean_instReprProjectionFunctionInfo_repr___redArg___closed__11_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_instReprAuxParentProjectionInfo_repr___redArg___closed__0:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_instReprAuxParentProjectionInfo_repr___redArg___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_instReprAuxParentProjectionInfo_repr___redArg___closed__1_value:
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
        core::ptr::addr_of!(l_Lean_instReprAuxParentProjectionInfo_repr___redArg___closed__0_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_instReprProjectionFunctionInfo_repr___redArg___closed__5_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_instReprAuxParentProjectionInfo_repr___redArg___closed__1:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_instReprAuxParentProjectionInfo_repr___redArg___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_instReprAuxParentProjectionInfo___closed__0_value:
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
    m_fun: l_Lean_instReprAuxParentProjectionInfo_repr___boxed as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_instReprAuxParentProjectionInfo___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_instReprAuxParentProjectionInfo___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Lean_instReprAuxParentProjectionInfo: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_instReprAuxParentProjectionInfo___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l___private_Lean_ProjFns_0__Lean_initFn___lam__0___closed__0_00___x40_Lean_ProjFns_496916995____hygCtx___hyg_2__value: crate::leanh::LeanArrayObject<0> = crate::leanh::LeanArrayObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<usize>()*2 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 246 }, m_size: 0, m_capacity: 0, m_data: [] };
static mut l___private_Lean_ProjFns_0__Lean_initFn___lam__0___closed__0_00___x40_Lean_ProjFns_496916995____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_ProjFns_0__Lean_initFn___lam__0___closed__0_00___x40_Lean_ProjFns_496916995____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_ProjFns_0__Lean_initFn___lam__0___closed__1_00___x40_Lean_ProjFns_496916995____hygCtx___hyg_2__value: crate::leanh::LeanArrayObject<0> = crate::leanh::LeanArrayObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<usize>()*2 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 246 }, m_size: 0, m_capacity: 0, m_data: [] };
static mut l___private_Lean_ProjFns_0__Lean_initFn___lam__0___closed__1_00___x40_Lean_ProjFns_496916995____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_ProjFns_0__Lean_initFn___lam__0___closed__1_00___x40_Lean_ProjFns_496916995____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_ProjFns_0__Lean_initFn___lam__0___closed__2_00___x40_Lean_ProjFns_496916995____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*3 + 0) as u16, other: 3, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Lean_ProjFns_0__Lean_initFn___lam__0___closed__1_00___x40_Lean_ProjFns_496916995____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_ProjFns_0__Lean_initFn___lam__0___closed__1_00___x40_Lean_ProjFns_496916995____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_ProjFns_0__Lean_initFn___lam__0___closed__1_00___x40_Lean_ProjFns_496916995____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_ProjFns_0__Lean_initFn___lam__0___closed__2_00___x40_Lean_ProjFns_496916995____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_ProjFns_0__Lean_initFn___lam__0___closed__2_00___x40_Lean_ProjFns_496916995____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_ProjFns_0__Lean_initFn___closed__0_00___x40_Lean_ProjFns_496916995____hygCtx___hyg_2__value: crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l___private_Lean_ProjFns_0__Lean_initFn___lam__0_00___x40_Lean_ProjFns_496916995____hygCtx___hyg_2____boxed as *const core::ffi::c_void, m_arity: 2, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_ProjFns_0__Lean_initFn___closed__0_00___x40_Lean_ProjFns_496916995____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_ProjFns_0__Lean_initFn___closed__0_00___x40_Lean_ProjFns_496916995____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_ProjFns_0__Lean_initFn___closed__1_00___x40_Lean_ProjFns_496916995____hygCtx___hyg_2__value: crate::leanh::LeanStringObject<21> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 21, m_capacity: 21, m_length: 20, m_data: [97, 117, 120, 80, 97, 114, 101, 110, 116, 80, 114, 111, 106, 73, 110, 102, 111, 69, 120, 116, 0]};
static mut l___private_Lean_ProjFns_0__Lean_initFn___closed__1_00___x40_Lean_ProjFns_496916995____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_ProjFns_0__Lean_initFn___closed__1_00___x40_Lean_ProjFns_496916995____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
static l___private_Lean_ProjFns_0__Lean_initFn___closed__2_00___x40_Lean_ProjFns_496916995____hygCtx___hyg_2__value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_ProjFns_0__Lean_initFn___closed__1_00___x40_Lean_ProjFns_2268652983____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_ProjFns_0__Lean_initFn___closed__2_00___x40_Lean_ProjFns_496916995____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_ProjFns_0__Lean_initFn___closed__2_00___x40_Lean_ProjFns_496916995____hygCtx___hyg_2__value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_ProjFns_0__Lean_initFn___closed__1_00___x40_Lean_ProjFns_496916995____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,3130712378843676676 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_ProjFns_0__Lean_initFn___closed__2_00___x40_Lean_ProjFns_496916995____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_ProjFns_0__Lean_initFn___closed__2_00___x40_Lean_ProjFns_496916995____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static mut l_Lean_auxParentProjInfoExt: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub unsafe fn l_Nat_cast___at___00Lean_instReprProjectionFunctionInfo_repr_spec__0(
    mut v_a_488_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_489_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_489_ = lean_nat_to_int(v_a_488_);
    return v___x_489_;
}
pub unsafe fn _init_l_Lean_instReprProjectionFunctionInfo_repr___redArg___closed__7()
-> *mut crate::leanh::LeanObject {
    let mut v___x_503_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_504_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_503_ = crate::leanh::lean_unsigned_to_nat(12);
    v___x_504_ = lean_nat_to_int(v___x_503_);
    return v___x_504_;
}
pub unsafe fn _init_l_Lean_instReprProjectionFunctionInfo_repr___redArg___closed__12()
-> *mut crate::leanh::LeanObject {
    let mut v___x_511_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_512_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_511_ = crate::leanh::lean_unsigned_to_nat(13);
    v___x_512_ = lean_nat_to_int(v___x_511_);
    return v___x_512_;
}
pub unsafe fn _init_l_Lean_instReprProjectionFunctionInfo_repr___redArg___closed__15()
-> *mut crate::leanh::LeanObject {
    let mut v___x_516_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_517_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_516_ = crate::leanh::lean_unsigned_to_nat(5);
    v___x_517_ = lean_nat_to_int(v___x_516_);
    return v___x_517_;
}
pub unsafe fn _init_l_Lean_instReprProjectionFunctionInfo_repr___redArg___closed__19()
-> *mut crate::leanh::LeanObject {
    let mut v___x_522_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_523_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_522_ = l_Lean_instReprProjectionFunctionInfo_repr___redArg___closed__0;
    v___x_523_ = lean_string_length(v___x_522_);
    return v___x_523_;
}
pub unsafe fn _init_l_Lean_instReprProjectionFunctionInfo_repr___redArg___closed__20()
-> *mut crate::leanh::LeanObject {
    let mut v___x_524_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_525_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_524_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_instReprProjectionFunctionInfo_repr___redArg___closed__19),
        core::ptr::addr_of_mut!(
            l_Lean_instReprProjectionFunctionInfo_repr___redArg___closed__19_once
        ),
        _init_l_Lean_instReprProjectionFunctionInfo_repr___redArg___closed__19,
    );
    v___x_525_ = lean_nat_to_int(v___x_524_);
    return v___x_525_;
}
pub unsafe fn l_Lean_instReprProjectionFunctionInfo_repr___redArg(
    mut v_x_530_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_ctorName_531_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_numParams_532_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_i_533_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fromClass_534_: u8 = 0;
    let mut v___x_535_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_536_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_537_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_538_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_539_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_540_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_541_: u8 = 0;
    let mut v___x_542_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_543_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_544_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_545_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_546_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_547_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_548_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_549_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_550_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_551_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_552_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_553_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_554_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_555_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_556_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_557_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_558_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_559_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_560_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_561_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_562_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_563_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_564_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_565_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_566_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_567_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_568_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_569_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_570_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_571_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_572_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_573_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_574_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_575_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_576_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_577_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_578_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_579_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_580_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_581_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_582_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_583_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_ctorName_531_ = crate::leanh::lean_ctor_get(v_x_530_, 0);
    crate::leanh::lean_inc(v_ctorName_531_);
    v_numParams_532_ = crate::leanh::lean_ctor_get(v_x_530_, 1);
    crate::leanh::lean_inc(v_numParams_532_);
    v_i_533_ = crate::leanh::lean_ctor_get(v_x_530_, 2);
    crate::leanh::lean_inc(v_i_533_);
    v_fromClass_534_ = crate::leanh::lean_ctor_get_uint8(
        v_x_530_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3) as u32,
    );
    crate::leanh::lean_dec_ref(v_x_530_);
    v___x_535_ = l_Lean_instReprProjectionFunctionInfo_repr___redArg___closed__5;
    v___x_536_ = l_Lean_instReprProjectionFunctionInfo_repr___redArg___closed__6;
    v___x_537_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_instReprProjectionFunctionInfo_repr___redArg___closed__7),
        core::ptr::addr_of_mut!(
            l_Lean_instReprProjectionFunctionInfo_repr___redArg___closed__7_once
        ),
        _init_l_Lean_instReprProjectionFunctionInfo_repr___redArg___closed__7,
    );
    v___x_538_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_539_ = l_Lean_Name_reprPrec(v_ctorName_531_, v___x_538_);
    v___x_540_ = crate::leanh::lean_alloc_ctor(4, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_540_, 0, v___x_537_);
    crate::leanh::lean_ctor_set(v___x_540_, 1, v___x_539_);
    v___x_541_ = 0;
    v___x_542_ = crate::leanh::lean_alloc_ctor(6, 1, (1) as u32);
    crate::leanh::lean_ctor_set(v___x_542_, 0, v___x_540_);
    crate::leanh::lean_ctor_set_uint8(
        v___x_542_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
        v___x_541_,
    );
    v___x_543_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_543_, 0, v___x_536_);
    crate::leanh::lean_ctor_set(v___x_543_, 1, v___x_542_);
    v___x_544_ = l_Lean_instReprProjectionFunctionInfo_repr___redArg___closed__9;
    v___x_545_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_545_, 0, v___x_543_);
    crate::leanh::lean_ctor_set(v___x_545_, 1, v___x_544_);
    v___x_546_ = crate::leanh::lean_box(1);
    v___x_547_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_547_, 0, v___x_545_);
    crate::leanh::lean_ctor_set(v___x_547_, 1, v___x_546_);
    v___x_548_ = l_Lean_instReprProjectionFunctionInfo_repr___redArg___closed__11;
    v___x_549_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_549_, 0, v___x_547_);
    crate::leanh::lean_ctor_set(v___x_549_, 1, v___x_548_);
    v___x_550_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_550_, 0, v___x_549_);
    crate::leanh::lean_ctor_set(v___x_550_, 1, v___x_535_);
    v___x_551_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_instReprProjectionFunctionInfo_repr___redArg___closed__12),
        core::ptr::addr_of_mut!(
            l_Lean_instReprProjectionFunctionInfo_repr___redArg___closed__12_once
        ),
        _init_l_Lean_instReprProjectionFunctionInfo_repr___redArg___closed__12,
    );
    v___x_552_ = l_Nat_reprFast(v_numParams_532_);
    v___x_553_ = crate::leanh::lean_alloc_ctor(3, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_553_, 0, v___x_552_);
    v___x_554_ = crate::leanh::lean_alloc_ctor(4, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_554_, 0, v___x_551_);
    crate::leanh::lean_ctor_set(v___x_554_, 1, v___x_553_);
    v___x_555_ = crate::leanh::lean_alloc_ctor(6, 1, (1) as u32);
    crate::leanh::lean_ctor_set(v___x_555_, 0, v___x_554_);
    crate::leanh::lean_ctor_set_uint8(
        v___x_555_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
        v___x_541_,
    );
    v___x_556_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_556_, 0, v___x_550_);
    crate::leanh::lean_ctor_set(v___x_556_, 1, v___x_555_);
    v___x_557_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_557_, 0, v___x_556_);
    crate::leanh::lean_ctor_set(v___x_557_, 1, v___x_544_);
    v___x_558_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_558_, 0, v___x_557_);
    crate::leanh::lean_ctor_set(v___x_558_, 1, v___x_546_);
    v___x_559_ = l_Lean_instReprProjectionFunctionInfo_repr___redArg___closed__14;
    v___x_560_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_560_, 0, v___x_558_);
    crate::leanh::lean_ctor_set(v___x_560_, 1, v___x_559_);
    v___x_561_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_561_, 0, v___x_560_);
    crate::leanh::lean_ctor_set(v___x_561_, 1, v___x_535_);
    v___x_562_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_instReprProjectionFunctionInfo_repr___redArg___closed__15),
        core::ptr::addr_of_mut!(
            l_Lean_instReprProjectionFunctionInfo_repr___redArg___closed__15_once
        ),
        _init_l_Lean_instReprProjectionFunctionInfo_repr___redArg___closed__15,
    );
    v___x_563_ = l_Nat_reprFast(v_i_533_);
    v___x_564_ = crate::leanh::lean_alloc_ctor(3, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_564_, 0, v___x_563_);
    v___x_565_ = crate::leanh::lean_alloc_ctor(4, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_565_, 0, v___x_562_);
    crate::leanh::lean_ctor_set(v___x_565_, 1, v___x_564_);
    v___x_566_ = crate::leanh::lean_alloc_ctor(6, 1, (1) as u32);
    crate::leanh::lean_ctor_set(v___x_566_, 0, v___x_565_);
    crate::leanh::lean_ctor_set_uint8(
        v___x_566_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
        v___x_541_,
    );
    v___x_567_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_567_, 0, v___x_561_);
    crate::leanh::lean_ctor_set(v___x_567_, 1, v___x_566_);
    v___x_568_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_568_, 0, v___x_567_);
    crate::leanh::lean_ctor_set(v___x_568_, 1, v___x_544_);
    v___x_569_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_569_, 0, v___x_568_);
    crate::leanh::lean_ctor_set(v___x_569_, 1, v___x_546_);
    v___x_570_ = l_Lean_instReprProjectionFunctionInfo_repr___redArg___closed__17;
    v___x_571_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_571_, 0, v___x_569_);
    crate::leanh::lean_ctor_set(v___x_571_, 1, v___x_570_);
    v___x_572_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_572_, 0, v___x_571_);
    crate::leanh::lean_ctor_set(v___x_572_, 1, v___x_535_);
    v___x_573_ = l_Bool_repr___redArg(v_fromClass_534_);
    v___x_574_ = crate::leanh::lean_alloc_ctor(4, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_574_, 0, v___x_551_);
    crate::leanh::lean_ctor_set(v___x_574_, 1, v___x_573_);
    v___x_575_ = crate::leanh::lean_alloc_ctor(6, 1, (1) as u32);
    crate::leanh::lean_ctor_set(v___x_575_, 0, v___x_574_);
    crate::leanh::lean_ctor_set_uint8(
        v___x_575_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
        v___x_541_,
    );
    v___x_576_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_576_, 0, v___x_572_);
    crate::leanh::lean_ctor_set(v___x_576_, 1, v___x_575_);
    v___x_577_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_instReprProjectionFunctionInfo_repr___redArg___closed__20),
        core::ptr::addr_of_mut!(
            l_Lean_instReprProjectionFunctionInfo_repr___redArg___closed__20_once
        ),
        _init_l_Lean_instReprProjectionFunctionInfo_repr___redArg___closed__20,
    );
    v___x_578_ = l_Lean_instReprProjectionFunctionInfo_repr___redArg___closed__21;
    v___x_579_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_579_, 0, v___x_578_);
    crate::leanh::lean_ctor_set(v___x_579_, 1, v___x_576_);
    v___x_580_ = l_Lean_instReprProjectionFunctionInfo_repr___redArg___closed__22;
    v___x_581_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_581_, 0, v___x_579_);
    crate::leanh::lean_ctor_set(v___x_581_, 1, v___x_580_);
    v___x_582_ = crate::leanh::lean_alloc_ctor(4, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_582_, 0, v___x_577_);
    crate::leanh::lean_ctor_set(v___x_582_, 1, v___x_581_);
    v___x_583_ = crate::leanh::lean_alloc_ctor(6, 1, (1) as u32);
    crate::leanh::lean_ctor_set(v___x_583_, 0, v___x_582_);
    crate::leanh::lean_ctor_set_uint8(
        v___x_583_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
        v___x_541_,
    );
    return v___x_583_;
}
pub unsafe fn l_Lean_instReprProjectionFunctionInfo_repr(
    mut v_x_584_: *mut crate::leanh::LeanObject,
    mut v_prec_585_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_586_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_586_ = l_Lean_instReprProjectionFunctionInfo_repr___redArg(v_x_584_);
    return v___x_586_;
}
pub unsafe fn l_Lean_instReprProjectionFunctionInfo_repr___boxed(
    mut v_x_587_: *mut crate::leanh::LeanObject,
    mut v_prec_588_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_589_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_589_ = l_Lean_instReprProjectionFunctionInfo_repr(v_x_587_, v_prec_588_);
    crate::leanh::lean_dec(v_prec_588_);
    return v_res_589_;
}
pub unsafe fn lean_mk_projection_info(
    mut v_ctorName_592_: *mut crate::leanh::LeanObject,
    mut v_numParams_593_: *mut crate::leanh::LeanObject,
    mut v_i_594_: *mut crate::leanh::LeanObject,
    mut v_fromClass_595_: u8,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_596_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_596_ = crate::leanh::lean_alloc_ctor(0, 3, (1) as u32);
    crate::leanh::lean_ctor_set(v___x_596_, 0, v_ctorName_592_);
    crate::leanh::lean_ctor_set(v___x_596_, 1, v_numParams_593_);
    crate::leanh::lean_ctor_set(v___x_596_, 2, v_i_594_);
    crate::leanh::lean_ctor_set_uint8(
        v___x_596_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3) as u32,
        v_fromClass_595_,
    );
    return v___x_596_;
}
pub unsafe fn l_Lean_mkProjectionInfoEx___boxed(
    mut v_ctorName_597_: *mut crate::leanh::LeanObject,
    mut v_numParams_598_: *mut crate::leanh::LeanObject,
    mut v_i_599_: *mut crate::leanh::LeanObject,
    mut v_fromClass_600_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_fromClass_boxed_601_: u8 = 0;
    let mut v_res_602_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_fromClass_boxed_601_ = (crate::leanh::lean_unbox(v_fromClass_600_) as u8);
    v_res_602_ = lean_mk_projection_info(
        v_ctorName_597_,
        v_numParams_598_,
        v_i_599_,
        v_fromClass_boxed_601_,
    );
    return v_res_602_;
}
pub unsafe fn lean_projection_info_from_class(
    mut v_info_603_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v_fromClass_604_: u8 = 0;
    v_fromClass_604_ = crate::leanh::lean_ctor_get_uint8(
        v_info_603_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3) as u32,
    );
    crate::leanh::lean_dec_ref(v_info_603_);
    return v_fromClass_604_;
}
pub unsafe fn l_Lean_ProjectionFunctionInfo_fromClassEx___boxed(
    mut v_info_605_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_606_: u8 = 0;
    let mut v_r_607_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_606_ = lean_projection_info_from_class(v_info_605_);
    v_r_607_ = crate::leanh::lean_box((v_res_606_) as usize);
    return v_r_607_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_ProjFns_0__Lean_initFn_00___x40_Lean_ProjFns_2268652983____hygCtx___hyg_2__spec__0_spec__0(
    mut v_init_608_: *mut crate::leanh::LeanObject,
    mut v_x_609_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_k_610_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_611_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_l_612_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_613_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_614_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_615_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_616_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_609_) == 0 {
                    v_k_610_ = crate::leanh::lean_ctor_get(v_x_609_, 1);
                    v_v_611_ = crate::leanh::lean_ctor_get(v_x_609_, 2);
                    v_l_612_ = crate::leanh::lean_ctor_get(v_x_609_, 3);
                    v_r_613_ = crate::leanh::lean_ctor_get(v_x_609_, 4);
                    v___x_614_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_ProjFns_0__Lean_initFn_00___x40_Lean_ProjFns_2268652983____hygCtx___hyg_2__spec__0_spec__0(v_init_608_, v_l_612_);
                    crate::leanh::lean_inc(v_v_611_);
                    crate::leanh::lean_inc(v_k_610_);
                    v___x_615_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_615_, 0, v_k_610_);
                    crate::leanh::lean_ctor_set(v___x_615_, 1, v_v_611_);
                    v___x_616_ = lean_array_push(v___x_614_, v___x_615_);
                    v_init_608_ = v___x_616_;
                    v_x_609_ = v_r_613_;
                    state = 0;
                    continue;
                } else {
                    return v_init_608_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_ProjFns_0__Lean_initFn_00___x40_Lean_ProjFns_2268652983____hygCtx___hyg_2__spec__0_spec__0___boxed(
    mut v_init_618_: *mut crate::leanh::LeanObject,
    mut v_x_619_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_620_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_620_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_ProjFns_0__Lean_initFn_00___x40_Lean_ProjFns_2268652983____hygCtx___hyg_2__spec__0_spec__0(v_init_618_, v_x_619_);
    crate::leanh::lean_dec(v_x_619_);
    return v_res_620_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_ProjFns_0__Lean_initFn_00___x40_Lean_ProjFns_2268652983____hygCtx___hyg_2__spec__1(
    mut v_env_621_: *mut crate::leanh::LeanObject,
    mut v_as_622_: *mut crate::leanh::LeanObject,
    mut v_i_623_: usize,
    mut v_stop_624_: usize,
    mut v_b_625_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___y_627_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_628_: usize = 0;
    let mut v___x_629_: usize = 0;
    let mut v___x_631_: u8 = 0;
    let mut v___x_632_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_633_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_634_: u8 = 0;
    let mut v___x_635_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_631_ = lean_usize_dec_eq(v_i_623_, v_stop_624_);
                if v___x_631_ == 0 {
                    v___x_632_ = lean_array_uget_borrowed(v_as_622_, v_i_623_);
                    v_fst_633_ = crate::leanh::lean_ctor_get(v___x_632_, 0);
                    crate::leanh::lean_inc(v_fst_633_);
                    crate::leanh::lean_inc_ref(v_env_621_);
                    v___x_634_ = l_Lean_Environment_contains(v_env_621_, v_fst_633_, v___x_631_);
                    if v___x_634_ == 0 {
                        v___y_627_ = v_b_625_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v___x_632_);
                        v___x_635_ = lean_array_push(v_b_625_, v___x_632_);
                        v___y_627_ = v___x_635_;
                        state = 1;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_env_621_);
                    return v_b_625_;
                }
            }
            1 => {
                v___x_628_ = 1usize;
                v___x_629_ = lean_usize_add(v_i_623_, v___x_628_);
                v_i_623_ = v___x_629_;
                v_b_625_ = v___y_627_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_ProjFns_0__Lean_initFn_00___x40_Lean_ProjFns_2268652983____hygCtx___hyg_2__spec__1___boxed(
    mut v_env_636_: *mut crate::leanh::LeanObject,
    mut v_as_637_: *mut crate::leanh::LeanObject,
    mut v_i_638_: *mut crate::leanh::LeanObject,
    mut v_stop_639_: *mut crate::leanh::LeanObject,
    mut v_b_640_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_i_boxed_641_: usize = 0;
    let mut v_stop_boxed_642_: usize = 0;
    let mut v_res_643_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_i_boxed_641_ = crate::leanh::lean_unbox_usize(v_i_638_);
    crate::leanh::lean_dec(v_i_638_);
    v_stop_boxed_642_ = crate::leanh::lean_unbox_usize(v_stop_639_);
    crate::leanh::lean_dec(v_stop_639_);
    v_res_643_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_ProjFns_0__Lean_initFn_00___x40_Lean_ProjFns_2268652983____hygCtx___hyg_2__spec__1(v_env_636_, v_as_637_, v_i_boxed_641_, v_stop_boxed_642_, v_b_640_);
    crate::leanh::lean_dec_ref(v_as_637_);
    return v_res_643_;
}
pub unsafe fn l___private_Lean_ProjFns_0__Lean_initFn___lam__0_00___x40_Lean_ProjFns_2268652983____hygCtx___hyg_2_(
    mut v_env_650_: *mut crate::leanh::LeanObject,
    mut v_s_651_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_652_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_653_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_654_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_655_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_656_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_657_: u8 = 0;
    v___x_652_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_653_ = l___private_Lean_ProjFns_0__Lean_initFn___lam__0___closed__0_00___x40_Lean_ProjFns_2268652983____hygCtx___hyg_2_;
    v___x_654_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_ProjFns_0__Lean_initFn_00___x40_Lean_ProjFns_2268652983____hygCtx___hyg_2__spec__0_spec__0(v___x_653_, v_s_651_);
    v___x_655_ = lean_array_get_size(v___x_654_);
    v___x_656_ = l___private_Lean_ProjFns_0__Lean_initFn___lam__0___closed__1_00___x40_Lean_ProjFns_2268652983____hygCtx___hyg_2_;
    v___x_657_ = lean_nat_dec_lt(v___x_652_, v___x_655_);
    if v___x_657_ == 0 {
        let mut v___x_658_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec_ref(v___x_654_);
        crate::leanh::lean_dec_ref(v_env_650_);
        v___x_658_ = l___private_Lean_ProjFns_0__Lean_initFn___lam__0___closed__2_00___x40_Lean_ProjFns_2268652983____hygCtx___hyg_2_;
        return v___x_658_;
    } else {
        let mut v___x_659_: u8 = 0;
        v___x_659_ = lean_nat_dec_le(v___x_655_, v___x_655_);
        if v___x_659_ == 0 {
            if v___x_657_ == 0 {
                let mut v___x_660_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                crate::leanh::lean_dec_ref(v___x_654_);
                crate::leanh::lean_dec_ref(v_env_650_);
                v___x_660_ = l___private_Lean_ProjFns_0__Lean_initFn___lam__0___closed__2_00___x40_Lean_ProjFns_2268652983____hygCtx___hyg_2_;
                return v___x_660_;
            } else {
                let mut v___x_661_: usize = 0;
                let mut v___x_662_: usize = 0;
                let mut v___x_663_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_664_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                v___x_661_ = 0usize;
                v___x_662_ = lean_usize_of_nat(v___x_655_);
                v___x_663_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_ProjFns_0__Lean_initFn_00___x40_Lean_ProjFns_2268652983____hygCtx___hyg_2__spec__1(v_env_650_, v___x_654_, v___x_661_, v___x_662_, v___x_656_);
                crate::leanh::lean_dec_ref(v___x_654_);
                crate::leanh::lean_inc_ref_n(v___x_663_, 2);
                v___x_664_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_664_, 0, v___x_663_);
                crate::leanh::lean_ctor_set(v___x_664_, 1, v___x_663_);
                crate::leanh::lean_ctor_set(v___x_664_, 2, v___x_663_);
                return v___x_664_;
            }
        } else {
            let mut v___x_665_: usize = 0;
            let mut v___x_666_: usize = 0;
            let mut v___x_667_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_668_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_665_ = 0usize;
            v___x_666_ = lean_usize_of_nat(v___x_655_);
            v___x_667_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_ProjFns_0__Lean_initFn_00___x40_Lean_ProjFns_2268652983____hygCtx___hyg_2__spec__1(v_env_650_, v___x_654_, v___x_665_, v___x_666_, v___x_656_);
            crate::leanh::lean_dec_ref(v___x_654_);
            crate::leanh::lean_inc_ref_n(v___x_667_, 2);
            v___x_668_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
            crate::leanh::lean_ctor_set(v___x_668_, 0, v___x_667_);
            crate::leanh::lean_ctor_set(v___x_668_, 1, v___x_667_);
            crate::leanh::lean_ctor_set(v___x_668_, 2, v___x_667_);
            return v___x_668_;
        }
    }
}
pub unsafe fn l___private_Lean_ProjFns_0__Lean_initFn___lam__0_00___x40_Lean_ProjFns_2268652983____hygCtx___hyg_2____boxed(
    mut v_env_669_: *mut crate::leanh::LeanObject,
    mut v_s_670_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_671_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_671_ = l___private_Lean_ProjFns_0__Lean_initFn___lam__0_00___x40_Lean_ProjFns_2268652983____hygCtx___hyg_2_(v_env_669_, v_s_670_);
    crate::leanh::lean_dec(v_s_670_);
    return v_res_671_;
}
pub unsafe fn l___private_Lean_ProjFns_0__Lean_initFn_00___x40_Lean_ProjFns_2268652983____hygCtx___hyg_2_()
-> *mut crate::leanh::LeanObject {
    let mut v___f_681_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_682_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_683_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_684_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_681_ = l___private_Lean_ProjFns_0__Lean_initFn___closed__0_00___x40_Lean_ProjFns_2268652983____hygCtx___hyg_2_;
    v___x_682_ = l___private_Lean_ProjFns_0__Lean_initFn___closed__3_00___x40_Lean_ProjFns_2268652983____hygCtx___hyg_2_;
    v___x_683_ = l___private_Lean_ProjFns_0__Lean_initFn___closed__4_00___x40_Lean_ProjFns_2268652983____hygCtx___hyg_2_;
    v___x_684_ = l_Lean_mkMapDeclarationExtension___redArg(v___x_682_, v___x_683_, v___f_681_);
    return v___x_684_;
}
pub unsafe fn l___private_Lean_ProjFns_0__Lean_initFn_00___x40_Lean_ProjFns_2268652983____hygCtx___hyg_2____boxed(
    mut v_a_685_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_686_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_686_ =
        l___private_Lean_ProjFns_0__Lean_initFn_00___x40_Lean_ProjFns_2268652983____hygCtx___hyg_2_(
        );
    return v_res_686_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_ProjFns_0__Lean_initFn_00___x40_Lean_ProjFns_2268652983____hygCtx___hyg_2__spec__0(
    mut v_init_687_: *mut crate::leanh::LeanObject,
    mut v_t_688_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_689_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_689_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_ProjFns_0__Lean_initFn_00___x40_Lean_ProjFns_2268652983____hygCtx___hyg_2__spec__0_spec__0(v_init_687_, v_t_688_);
    return v___x_689_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_ProjFns_0__Lean_initFn_00___x40_Lean_ProjFns_2268652983____hygCtx___hyg_2__spec__0___boxed(
    mut v_init_690_: *mut crate::leanh::LeanObject,
    mut v_t_691_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_692_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_692_ = l_Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_ProjFns_0__Lean_initFn_00___x40_Lean_ProjFns_2268652983____hygCtx___hyg_2__spec__0(v_init_690_, v_t_691_);
    crate::leanh::lean_dec(v_t_691_);
    return v_res_692_;
}
pub unsafe fn l_Lean_addProjectionFnInfo(
    mut v_env_693_: *mut crate::leanh::LeanObject,
    mut v_projName_694_: *mut crate::leanh::LeanObject,
    mut v_ctorName_695_: *mut crate::leanh::LeanObject,
    mut v_numParams_696_: *mut crate::leanh::LeanObject,
    mut v_i_697_: *mut crate::leanh::LeanObject,
    mut v_fromClass_698_: u8,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_699_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_700_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_701_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_699_ = l_Lean_projectionFnInfoExt;
    v___x_700_ = crate::leanh::lean_alloc_ctor(0, 3, (1) as u32);
    crate::leanh::lean_ctor_set(v___x_700_, 0, v_ctorName_695_);
    crate::leanh::lean_ctor_set(v___x_700_, 1, v_numParams_696_);
    crate::leanh::lean_ctor_set(v___x_700_, 2, v_i_697_);
    crate::leanh::lean_ctor_set_uint8(
        v___x_700_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3) as u32,
        v_fromClass_698_,
    );
    v___x_701_ = l_Lean_MapDeclarationExtension_insert___redArg(
        v___x_699_,
        v_env_693_,
        v_projName_694_,
        v___x_700_,
    );
    return v___x_701_;
}
pub unsafe fn l_Lean_addProjectionFnInfo___boxed(
    mut v_env_702_: *mut crate::leanh::LeanObject,
    mut v_projName_703_: *mut crate::leanh::LeanObject,
    mut v_ctorName_704_: *mut crate::leanh::LeanObject,
    mut v_numParams_705_: *mut crate::leanh::LeanObject,
    mut v_i_706_: *mut crate::leanh::LeanObject,
    mut v_fromClass_707_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_fromClass_boxed_708_: u8 = 0;
    let mut v_res_709_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_fromClass_boxed_708_ = (crate::leanh::lean_unbox(v_fromClass_707_) as u8);
    v_res_709_ = l_Lean_addProjectionFnInfo(
        v_env_702_,
        v_projName_703_,
        v_ctorName_704_,
        v_numParams_705_,
        v_i_706_,
        v_fromClass_boxed_708_,
    );
    return v_res_709_;
}
pub unsafe fn l_Lean_Environment_getProjectionFnInfo_x3f(
    mut v_env_710_: *mut crate::leanh::LeanObject,
    mut v_projName_711_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_712_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toEnvExtension_713_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_asyncMode_714_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_715_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_716_: u8 = 0;
    let mut v___x_717_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_712_ = l_Lean_projectionFnInfoExt;
    v_toEnvExtension_713_ = crate::leanh::lean_ctor_get(v___x_712_, 0);
    v_asyncMode_714_ = crate::leanh::lean_ctor_get(v_toEnvExtension_713_, 2);
    v___x_715_ = l_Lean_instInhabitedProjectionFunctionInfo_default;
    v___x_716_ = 0;
    v___x_717_ = l_Lean_MapDeclarationExtension_find_x3f___redArg(
        v___x_715_,
        v___x_712_,
        v_env_710_,
        v_projName_711_,
        v_asyncMode_714_,
        v___x_716_,
    );
    return v___x_717_;
}
pub unsafe fn l_Lean_Environment_isProjectionFn(
    mut v_env_718_: *mut crate::leanh::LeanObject,
    mut v_declName_719_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_720_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_721_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_722_: u8 = 0;
    v___x_720_ = l_Lean_instInhabitedProjectionFunctionInfo_default;
    v___x_721_ = l_Lean_projectionFnInfoExt;
    v___x_722_ = l_Lean_MapDeclarationExtension_contains___redArg(
        v___x_720_,
        v___x_721_,
        v_env_718_,
        v_declName_719_,
    );
    return v___x_722_;
}
pub unsafe fn l_Lean_Environment_isProjectionFn___boxed(
    mut v_env_723_: *mut crate::leanh::LeanObject,
    mut v_declName_724_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_725_: u8 = 0;
    let mut v_r_726_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_725_ = l_Lean_Environment_isProjectionFn(v_env_723_, v_declName_724_);
    v_r_726_ = crate::leanh::lean_box((v_res_725_) as usize);
    return v_r_726_;
}
pub unsafe fn l_Lean_Environment_getProjectionStructureName_x3f(
    mut v_env_727_: *mut crate::leanh::LeanObject,
    mut v_projName_728_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_729_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_730_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_731_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ctorName_732_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_733_: u8 = 0;
    let mut v___x_734_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_735_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_737_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_738_: u8 = 0;
    let mut v_val_739_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_induct_740_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_742_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_743_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_744_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_745_: u8 = 0;
    let mut v___x_746_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                crate::leanh::lean_inc_ref(v_env_727_);
                v___x_729_ =
                    l_Lean_Environment_getProjectionFnInfo_x3f(v_env_727_, v_projName_728_);
                if crate::leanh::lean_obj_tag(v___x_729_) == 0 {
                    crate::leanh::lean_dec_ref(v_env_727_);
                    v___x_730_ = crate::leanh::lean_box(0);
                    return v___x_730_;
                } else {
                    v_val_731_ = crate::leanh::lean_ctor_get(v___x_729_, 0);
                    crate::leanh::lean_inc(v_val_731_);
                    crate::leanh::lean_dec_ref_known(v___x_729_, 1);
                    v_ctorName_732_ = crate::leanh::lean_ctor_get(v_val_731_, 0);
                    crate::leanh::lean_inc(v_ctorName_732_);
                    crate::leanh::lean_dec(v_val_731_);
                    v___x_733_ = 0;
                    v___x_734_ =
                        l_Lean_Environment_find_x3f(v_env_727_, v_ctorName_732_, v___x_733_);
                    if crate::leanh::lean_obj_tag(v___x_734_) == 1 {
                        v_val_735_ = crate::leanh::lean_ctor_get(v___x_734_, 0);
                        v_isSharedCheck_745_ = (!crate::leanh::lean_is_exclusive(v___x_734_)) as u8;
                        if v_isSharedCheck_745_ == 0 {
                            v___x_737_ = v___x_734_;
                            v_isShared_738_ = v_isSharedCheck_745_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_val_735_);
                            crate::leanh::lean_dec(v___x_734_);
                            v___x_737_ = crate::leanh::lean_box(0);
                            v_isShared_738_ = v_isSharedCheck_745_;
                            state = 1;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec(v___x_734_);
                        v___x_746_ = crate::leanh::lean_box(0);
                        return v___x_746_;
                    }
                }
            }
            1 => {
                if crate::leanh::lean_obj_tag(v_val_735_) == 6 {
                    v_val_739_ = crate::leanh::lean_ctor_get(v_val_735_, 0);
                    crate::leanh::lean_inc_ref(v_val_739_);
                    crate::leanh::lean_dec_ref_known(v_val_735_, 1);
                    v_induct_740_ = crate::leanh::lean_ctor_get(v_val_739_, 1);
                    crate::leanh::lean_inc(v_induct_740_);
                    crate::leanh::lean_dec_ref(v_val_739_);
                    if v_isShared_738_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_737_, 0, v_induct_740_);
                        v___x_742_ = v___x_737_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_743_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_743_, 0, v_induct_740_);
                        v___x_742_ = v_reuseFailAlloc_743_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_737_);
                    crate::leanh::lean_dec(v_val_735_);
                    v___x_744_ = crate::leanh::lean_box(0);
                    return v___x_744_;
                }
            }
            2 => {
                return v___x_742_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_isProjectionFn___redArg___lam__0(
    mut v_declName_747_: *mut crate::leanh::LeanObject,
    mut v_toPure_748_: *mut crate::leanh::LeanObject,
    mut v_____do__lift_749_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_750_: u8 = 0;
    let mut v___x_751_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_752_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_750_ = l_Lean_Environment_isProjectionFn(v_____do__lift_749_, v_declName_747_);
    v___x_751_ = crate::leanh::lean_box((v___x_750_) as usize);
    v___x_752_ = crate::leanh::lean_apply_2(v_toPure_748_, crate::leanh::lean_box(0), v___x_751_);
    return v___x_752_;
}
pub unsafe fn l_Lean_isProjectionFn___redArg(
    mut v_inst_753_: *mut crate::leanh::LeanObject,
    mut v_inst_754_: *mut crate::leanh::LeanObject,
    mut v_declName_755_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toApplicative_756_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_757_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_getEnv_758_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_759_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_760_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_761_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_756_ = crate::leanh::lean_ctor_get(v_inst_754_, 0);
    crate::leanh::lean_inc_ref(v_toApplicative_756_);
    v_toBind_757_ = crate::leanh::lean_ctor_get(v_inst_754_, 1);
    crate::leanh::lean_inc(v_toBind_757_);
    crate::leanh::lean_dec_ref(v_inst_754_);
    v_getEnv_758_ = crate::leanh::lean_ctor_get(v_inst_753_, 0);
    crate::leanh::lean_inc(v_getEnv_758_);
    crate::leanh::lean_dec_ref(v_inst_753_);
    v_toPure_759_ = crate::leanh::lean_ctor_get(v_toApplicative_756_, 1);
    crate::leanh::lean_inc(v_toPure_759_);
    crate::leanh::lean_dec_ref(v_toApplicative_756_);
    v___f_760_ = crate::leanh::lean_alloc_closure(
        l_Lean_isProjectionFn___redArg___lam__0 as *mut core::ffi::c_void,
        3,
        2,
    );
    crate::leanh::lean_closure_set(v___f_760_, 0, v_declName_755_);
    crate::leanh::lean_closure_set(v___f_760_, 1, v_toPure_759_);
    v___x_761_ = crate::leanh::lean_apply_4(
        v_toBind_757_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v_getEnv_758_,
        v___f_760_,
    );
    return v___x_761_;
}
pub unsafe fn l_Lean_isProjectionFn(
    mut v_m_762_: *mut crate::leanh::LeanObject,
    mut v_inst_763_: *mut crate::leanh::LeanObject,
    mut v_inst_764_: *mut crate::leanh::LeanObject,
    mut v_declName_765_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_766_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_766_ = l_Lean_isProjectionFn___redArg(v_inst_763_, v_inst_764_, v_declName_765_);
    return v___x_766_;
}
pub unsafe fn l_Lean_getProjectionFnInfo_x3f___redArg___lam__0(
    mut v_declName_767_: *mut crate::leanh::LeanObject,
    mut v_toPure_768_: *mut crate::leanh::LeanObject,
    mut v_____do__lift_769_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_770_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_771_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_770_ = l_Lean_Environment_getProjectionFnInfo_x3f(v_____do__lift_769_, v_declName_767_);
    v___x_771_ = crate::leanh::lean_apply_2(v_toPure_768_, crate::leanh::lean_box(0), v___x_770_);
    return v___x_771_;
}
pub unsafe fn l_Lean_getProjectionFnInfo_x3f___redArg(
    mut v_inst_772_: *mut crate::leanh::LeanObject,
    mut v_inst_773_: *mut crate::leanh::LeanObject,
    mut v_declName_774_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toApplicative_775_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_776_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_getEnv_777_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_778_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_779_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_780_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_775_ = crate::leanh::lean_ctor_get(v_inst_773_, 0);
    crate::leanh::lean_inc_ref(v_toApplicative_775_);
    v_toBind_776_ = crate::leanh::lean_ctor_get(v_inst_773_, 1);
    crate::leanh::lean_inc(v_toBind_776_);
    crate::leanh::lean_dec_ref(v_inst_773_);
    v_getEnv_777_ = crate::leanh::lean_ctor_get(v_inst_772_, 0);
    crate::leanh::lean_inc(v_getEnv_777_);
    crate::leanh::lean_dec_ref(v_inst_772_);
    v_toPure_778_ = crate::leanh::lean_ctor_get(v_toApplicative_775_, 1);
    crate::leanh::lean_inc(v_toPure_778_);
    crate::leanh::lean_dec_ref(v_toApplicative_775_);
    v___f_779_ = crate::leanh::lean_alloc_closure(
        l_Lean_getProjectionFnInfo_x3f___redArg___lam__0 as *mut core::ffi::c_void,
        3,
        2,
    );
    crate::leanh::lean_closure_set(v___f_779_, 0, v_declName_774_);
    crate::leanh::lean_closure_set(v___f_779_, 1, v_toPure_778_);
    v___x_780_ = crate::leanh::lean_apply_4(
        v_toBind_776_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v_getEnv_777_,
        v___f_779_,
    );
    return v___x_780_;
}
pub unsafe fn l_Lean_getProjectionFnInfo_x3f(
    mut v_m_781_: *mut crate::leanh::LeanObject,
    mut v_inst_782_: *mut crate::leanh::LeanObject,
    mut v_inst_783_: *mut crate::leanh::LeanObject,
    mut v_declName_784_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_785_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_785_ = l_Lean_getProjectionFnInfo_x3f___redArg(v_inst_782_, v_inst_783_, v_declName_784_);
    return v___x_785_;
}
pub unsafe fn l_Lean_instReprAuxParentProjectionInfo_repr___redArg(
    mut v_x_797_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_numParams_798_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fromClass_799_: u8 = 0;
    let mut v___x_801_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_802_: u8 = 0;
    let mut v___x_803_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_804_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_805_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_806_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_807_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_808_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_809_: u8 = 0;
    let mut v___x_811_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_812_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_813_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_814_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_815_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_816_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_817_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_818_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_819_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_820_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_821_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_822_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_823_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_824_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_825_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_826_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_827_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_828_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_829_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_830_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_831_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_832_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_numParams_798_ = crate::leanh::lean_ctor_get(v_x_797_, 0);
                v_fromClass_799_ = crate::leanh::lean_ctor_get_uint8(
                    v_x_797_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                );
                v_isSharedCheck_832_ = (!crate::leanh::lean_is_exclusive(v_x_797_)) as u8;
                if v_isSharedCheck_832_ == 0 {
                    v___x_801_ = v_x_797_;
                    v_isShared_802_ = v_isSharedCheck_832_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_numParams_798_);
                    crate::leanh::lean_dec(v_x_797_);
                    v___x_801_ = crate::leanh::lean_box(0);
                    v_isShared_802_ = v_isSharedCheck_832_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_803_ = l_Lean_instReprProjectionFunctionInfo_repr___redArg___closed__5;
                v___x_804_ = l_Lean_instReprAuxParentProjectionInfo_repr___redArg___closed__1;
                v___x_805_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Lean_instReprProjectionFunctionInfo_repr___redArg___closed__12
                    ),
                    core::ptr::addr_of_mut!(
                        l_Lean_instReprProjectionFunctionInfo_repr___redArg___closed__12_once
                    ),
                    _init_l_Lean_instReprProjectionFunctionInfo_repr___redArg___closed__12,
                );
                v___x_806_ = l_Nat_reprFast(v_numParams_798_);
                v___x_807_ = crate::leanh::lean_alloc_ctor(3, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_807_, 0, v___x_806_);
                v___x_808_ = crate::leanh::lean_alloc_ctor(4, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_808_, 0, v___x_805_);
                crate::leanh::lean_ctor_set(v___x_808_, 1, v___x_807_);
                v___x_809_ = 0;
                if v_isShared_802_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_801_, 6);
                    crate::leanh::lean_ctor_set(v___x_801_, 0, v___x_808_);
                    v___x_811_ = v___x_801_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_831_ = crate::leanh::lean_alloc_ctor(6, 1, (1) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_831_, 0, v___x_808_);
                    v___x_811_ = v_reuseFailAlloc_831_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                crate::leanh::lean_ctor_set_uint8(
                    v___x_811_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                    v___x_809_,
                );
                v___x_812_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_812_, 0, v___x_804_);
                crate::leanh::lean_ctor_set(v___x_812_, 1, v___x_811_);
                v___x_813_ = l_Lean_instReprProjectionFunctionInfo_repr___redArg___closed__9;
                v___x_814_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_814_, 0, v___x_812_);
                crate::leanh::lean_ctor_set(v___x_814_, 1, v___x_813_);
                v___x_815_ = crate::leanh::lean_box(1);
                v___x_816_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_816_, 0, v___x_814_);
                crate::leanh::lean_ctor_set(v___x_816_, 1, v___x_815_);
                v___x_817_ = l_Lean_instReprProjectionFunctionInfo_repr___redArg___closed__17;
                v___x_818_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_818_, 0, v___x_816_);
                crate::leanh::lean_ctor_set(v___x_818_, 1, v___x_817_);
                v___x_819_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_819_, 0, v___x_818_);
                crate::leanh::lean_ctor_set(v___x_819_, 1, v___x_803_);
                v___x_820_ = l_Bool_repr___redArg(v_fromClass_799_);
                v___x_821_ = crate::leanh::lean_alloc_ctor(4, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_821_, 0, v___x_805_);
                crate::leanh::lean_ctor_set(v___x_821_, 1, v___x_820_);
                v___x_822_ = crate::leanh::lean_alloc_ctor(6, 1, (1) as u32);
                crate::leanh::lean_ctor_set(v___x_822_, 0, v___x_821_);
                crate::leanh::lean_ctor_set_uint8(
                    v___x_822_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                    v___x_809_,
                );
                v___x_823_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_823_, 0, v___x_819_);
                crate::leanh::lean_ctor_set(v___x_823_, 1, v___x_822_);
                v___x_824_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Lean_instReprProjectionFunctionInfo_repr___redArg___closed__20
                    ),
                    core::ptr::addr_of_mut!(
                        l_Lean_instReprProjectionFunctionInfo_repr___redArg___closed__20_once
                    ),
                    _init_l_Lean_instReprProjectionFunctionInfo_repr___redArg___closed__20,
                );
                v___x_825_ = l_Lean_instReprProjectionFunctionInfo_repr___redArg___closed__21;
                v___x_826_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_826_, 0, v___x_825_);
                crate::leanh::lean_ctor_set(v___x_826_, 1, v___x_823_);
                v___x_827_ = l_Lean_instReprProjectionFunctionInfo_repr___redArg___closed__22;
                v___x_828_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_828_, 0, v___x_826_);
                crate::leanh::lean_ctor_set(v___x_828_, 1, v___x_827_);
                v___x_829_ = crate::leanh::lean_alloc_ctor(4, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_829_, 0, v___x_824_);
                crate::leanh::lean_ctor_set(v___x_829_, 1, v___x_828_);
                v___x_830_ = crate::leanh::lean_alloc_ctor(6, 1, (1) as u32);
                crate::leanh::lean_ctor_set(v___x_830_, 0, v___x_829_);
                crate::leanh::lean_ctor_set_uint8(
                    v___x_830_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                    v___x_809_,
                );
                return v___x_830_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_instReprAuxParentProjectionInfo_repr(
    mut v_x_833_: *mut crate::leanh::LeanObject,
    mut v_prec_834_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_835_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_835_ = l_Lean_instReprAuxParentProjectionInfo_repr___redArg(v_x_833_);
    return v___x_835_;
}
pub unsafe fn l_Lean_instReprAuxParentProjectionInfo_repr___boxed(
    mut v_x_836_: *mut crate::leanh::LeanObject,
    mut v_prec_837_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_838_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_838_ = l_Lean_instReprAuxParentProjectionInfo_repr(v_x_836_, v_prec_837_);
    crate::leanh::lean_dec(v_prec_837_);
    return v_res_838_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_ProjFns_0__Lean_initFn_00___x40_Lean_ProjFns_496916995____hygCtx___hyg_2__spec__0_spec__0(
    mut v_init_841_: *mut crate::leanh::LeanObject,
    mut v_x_842_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_k_843_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_844_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_l_845_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_846_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_847_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_848_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_849_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_842_) == 0 {
                    v_k_843_ = crate::leanh::lean_ctor_get(v_x_842_, 1);
                    v_v_844_ = crate::leanh::lean_ctor_get(v_x_842_, 2);
                    v_l_845_ = crate::leanh::lean_ctor_get(v_x_842_, 3);
                    v_r_846_ = crate::leanh::lean_ctor_get(v_x_842_, 4);
                    v___x_847_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_ProjFns_0__Lean_initFn_00___x40_Lean_ProjFns_496916995____hygCtx___hyg_2__spec__0_spec__0(v_init_841_, v_l_845_);
                    crate::leanh::lean_inc(v_v_844_);
                    crate::leanh::lean_inc(v_k_843_);
                    v___x_848_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_848_, 0, v_k_843_);
                    crate::leanh::lean_ctor_set(v___x_848_, 1, v_v_844_);
                    v___x_849_ = lean_array_push(v___x_847_, v___x_848_);
                    v_init_841_ = v___x_849_;
                    v_x_842_ = v_r_846_;
                    state = 0;
                    continue;
                } else {
                    return v_init_841_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_ProjFns_0__Lean_initFn_00___x40_Lean_ProjFns_496916995____hygCtx___hyg_2__spec__0_spec__0___boxed(
    mut v_init_851_: *mut crate::leanh::LeanObject,
    mut v_x_852_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_853_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_853_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_ProjFns_0__Lean_initFn_00___x40_Lean_ProjFns_496916995____hygCtx___hyg_2__spec__0_spec__0(v_init_851_, v_x_852_);
    crate::leanh::lean_dec(v_x_852_);
    return v_res_853_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_ProjFns_0__Lean_initFn_00___x40_Lean_ProjFns_496916995____hygCtx___hyg_2__spec__1(
    mut v_env_854_: *mut crate::leanh::LeanObject,
    mut v_as_855_: *mut crate::leanh::LeanObject,
    mut v_i_856_: usize,
    mut v_stop_857_: usize,
    mut v_b_858_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___y_860_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_861_: usize = 0;
    let mut v___x_862_: usize = 0;
    let mut v___x_864_: u8 = 0;
    let mut v___x_865_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_866_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_867_: u8 = 0;
    let mut v___x_868_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_864_ = lean_usize_dec_eq(v_i_856_, v_stop_857_);
                if v___x_864_ == 0 {
                    v___x_865_ = lean_array_uget_borrowed(v_as_855_, v_i_856_);
                    v_fst_866_ = crate::leanh::lean_ctor_get(v___x_865_, 0);
                    crate::leanh::lean_inc(v_fst_866_);
                    crate::leanh::lean_inc_ref(v_env_854_);
                    v___x_867_ = l_Lean_Environment_contains(v_env_854_, v_fst_866_, v___x_864_);
                    if v___x_867_ == 0 {
                        v___y_860_ = v_b_858_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v___x_865_);
                        v___x_868_ = lean_array_push(v_b_858_, v___x_865_);
                        v___y_860_ = v___x_868_;
                        state = 1;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_env_854_);
                    return v_b_858_;
                }
            }
            1 => {
                v___x_861_ = 1usize;
                v___x_862_ = lean_usize_add(v_i_856_, v___x_861_);
                v_i_856_ = v___x_862_;
                v_b_858_ = v___y_860_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_ProjFns_0__Lean_initFn_00___x40_Lean_ProjFns_496916995____hygCtx___hyg_2__spec__1___boxed(
    mut v_env_869_: *mut crate::leanh::LeanObject,
    mut v_as_870_: *mut crate::leanh::LeanObject,
    mut v_i_871_: *mut crate::leanh::LeanObject,
    mut v_stop_872_: *mut crate::leanh::LeanObject,
    mut v_b_873_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_i_boxed_874_: usize = 0;
    let mut v_stop_boxed_875_: usize = 0;
    let mut v_res_876_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_i_boxed_874_ = crate::leanh::lean_unbox_usize(v_i_871_);
    crate::leanh::lean_dec(v_i_871_);
    v_stop_boxed_875_ = crate::leanh::lean_unbox_usize(v_stop_872_);
    crate::leanh::lean_dec(v_stop_872_);
    v_res_876_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_ProjFns_0__Lean_initFn_00___x40_Lean_ProjFns_496916995____hygCtx___hyg_2__spec__1(v_env_869_, v_as_870_, v_i_boxed_874_, v_stop_boxed_875_, v_b_873_);
    crate::leanh::lean_dec_ref(v_as_870_);
    return v_res_876_;
}
pub unsafe fn l___private_Lean_ProjFns_0__Lean_initFn___lam__0_00___x40_Lean_ProjFns_496916995____hygCtx___hyg_2_(
    mut v_env_883_: *mut crate::leanh::LeanObject,
    mut v_s_884_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_885_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_886_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_887_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_888_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_889_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_890_: u8 = 0;
    v___x_885_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_886_ = l___private_Lean_ProjFns_0__Lean_initFn___lam__0___closed__0_00___x40_Lean_ProjFns_496916995____hygCtx___hyg_2_;
    v___x_887_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_ProjFns_0__Lean_initFn_00___x40_Lean_ProjFns_496916995____hygCtx___hyg_2__spec__0_spec__0(v___x_886_, v_s_884_);
    v___x_888_ = lean_array_get_size(v___x_887_);
    v___x_889_ = l___private_Lean_ProjFns_0__Lean_initFn___lam__0___closed__1_00___x40_Lean_ProjFns_496916995____hygCtx___hyg_2_;
    v___x_890_ = lean_nat_dec_lt(v___x_885_, v___x_888_);
    if v___x_890_ == 0 {
        let mut v___x_891_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec_ref(v___x_887_);
        crate::leanh::lean_dec_ref(v_env_883_);
        v___x_891_ = l___private_Lean_ProjFns_0__Lean_initFn___lam__0___closed__2_00___x40_Lean_ProjFns_496916995____hygCtx___hyg_2_;
        return v___x_891_;
    } else {
        let mut v___x_892_: u8 = 0;
        v___x_892_ = lean_nat_dec_le(v___x_888_, v___x_888_);
        if v___x_892_ == 0 {
            if v___x_890_ == 0 {
                let mut v___x_893_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                crate::leanh::lean_dec_ref(v___x_887_);
                crate::leanh::lean_dec_ref(v_env_883_);
                v___x_893_ = l___private_Lean_ProjFns_0__Lean_initFn___lam__0___closed__2_00___x40_Lean_ProjFns_496916995____hygCtx___hyg_2_;
                return v___x_893_;
            } else {
                let mut v___x_894_: usize = 0;
                let mut v___x_895_: usize = 0;
                let mut v___x_896_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_897_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                v___x_894_ = 0usize;
                v___x_895_ = lean_usize_of_nat(v___x_888_);
                v___x_896_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_ProjFns_0__Lean_initFn_00___x40_Lean_ProjFns_496916995____hygCtx___hyg_2__spec__1(v_env_883_, v___x_887_, v___x_894_, v___x_895_, v___x_889_);
                crate::leanh::lean_dec_ref(v___x_887_);
                crate::leanh::lean_inc_ref_n(v___x_896_, 2);
                v___x_897_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_897_, 0, v___x_896_);
                crate::leanh::lean_ctor_set(v___x_897_, 1, v___x_896_);
                crate::leanh::lean_ctor_set(v___x_897_, 2, v___x_896_);
                return v___x_897_;
            }
        } else {
            let mut v___x_898_: usize = 0;
            let mut v___x_899_: usize = 0;
            let mut v___x_900_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_901_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_898_ = 0usize;
            v___x_899_ = lean_usize_of_nat(v___x_888_);
            v___x_900_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_ProjFns_0__Lean_initFn_00___x40_Lean_ProjFns_496916995____hygCtx___hyg_2__spec__1(v_env_883_, v___x_887_, v___x_898_, v___x_899_, v___x_889_);
            crate::leanh::lean_dec_ref(v___x_887_);
            crate::leanh::lean_inc_ref_n(v___x_900_, 2);
            v___x_901_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
            crate::leanh::lean_ctor_set(v___x_901_, 0, v___x_900_);
            crate::leanh::lean_ctor_set(v___x_901_, 1, v___x_900_);
            crate::leanh::lean_ctor_set(v___x_901_, 2, v___x_900_);
            return v___x_901_;
        }
    }
}
pub unsafe fn l___private_Lean_ProjFns_0__Lean_initFn___lam__0_00___x40_Lean_ProjFns_496916995____hygCtx___hyg_2____boxed(
    mut v_env_902_: *mut crate::leanh::LeanObject,
    mut v_s_903_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_904_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_904_ = l___private_Lean_ProjFns_0__Lean_initFn___lam__0_00___x40_Lean_ProjFns_496916995____hygCtx___hyg_2_(v_env_902_, v_s_903_);
    crate::leanh::lean_dec(v_s_903_);
    return v_res_904_;
}
pub unsafe fn l___private_Lean_ProjFns_0__Lean_initFn_00___x40_Lean_ProjFns_496916995____hygCtx___hyg_2_()
-> *mut crate::leanh::LeanObject {
    let mut v___f_911_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_912_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_913_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_914_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_911_ = l___private_Lean_ProjFns_0__Lean_initFn___closed__0_00___x40_Lean_ProjFns_496916995____hygCtx___hyg_2_;
    v___x_912_ = l___private_Lean_ProjFns_0__Lean_initFn___closed__2_00___x40_Lean_ProjFns_496916995____hygCtx___hyg_2_;
    v___x_913_ = l___private_Lean_ProjFns_0__Lean_initFn___closed__4_00___x40_Lean_ProjFns_2268652983____hygCtx___hyg_2_;
    v___x_914_ = l_Lean_mkMapDeclarationExtension___redArg(v___x_912_, v___x_913_, v___f_911_);
    return v___x_914_;
}
pub unsafe fn l___private_Lean_ProjFns_0__Lean_initFn_00___x40_Lean_ProjFns_496916995____hygCtx___hyg_2____boxed(
    mut v_a_915_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_916_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_916_ =
        l___private_Lean_ProjFns_0__Lean_initFn_00___x40_Lean_ProjFns_496916995____hygCtx___hyg_2_(
        );
    return v_res_916_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_ProjFns_0__Lean_initFn_00___x40_Lean_ProjFns_496916995____hygCtx___hyg_2__spec__0(
    mut v_init_917_: *mut crate::leanh::LeanObject,
    mut v_t_918_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_919_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_919_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_ProjFns_0__Lean_initFn_00___x40_Lean_ProjFns_496916995____hygCtx___hyg_2__spec__0_spec__0(v_init_917_, v_t_918_);
    return v___x_919_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_ProjFns_0__Lean_initFn_00___x40_Lean_ProjFns_496916995____hygCtx___hyg_2__spec__0___boxed(
    mut v_init_920_: *mut crate::leanh::LeanObject,
    mut v_t_921_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_922_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_922_ = l_Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_ProjFns_0__Lean_initFn_00___x40_Lean_ProjFns_496916995____hygCtx___hyg_2__spec__0(v_init_920_, v_t_921_);
    crate::leanh::lean_dec(v_t_921_);
    return v_res_922_;
}
pub unsafe fn l_Lean_addAuxParentProjectionInfo(
    mut v_env_923_: *mut crate::leanh::LeanObject,
    mut v_projName_924_: *mut crate::leanh::LeanObject,
    mut v_numParams_925_: *mut crate::leanh::LeanObject,
    mut v_fromClass_926_: u8,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_927_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_928_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_929_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_927_ = l_Lean_auxParentProjInfoExt;
    v___x_928_ = crate::leanh::lean_alloc_ctor(0, 1, (1) as u32);
    crate::leanh::lean_ctor_set(v___x_928_, 0, v_numParams_925_);
    crate::leanh::lean_ctor_set_uint8(
        v___x_928_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
        v_fromClass_926_,
    );
    v___x_929_ = l_Lean_MapDeclarationExtension_insert___redArg(
        v___x_927_,
        v_env_923_,
        v_projName_924_,
        v___x_928_,
    );
    return v___x_929_;
}
pub unsafe fn l_Lean_addAuxParentProjectionInfo___boxed(
    mut v_env_930_: *mut crate::leanh::LeanObject,
    mut v_projName_931_: *mut crate::leanh::LeanObject,
    mut v_numParams_932_: *mut crate::leanh::LeanObject,
    mut v_fromClass_933_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_fromClass_boxed_934_: u8 = 0;
    let mut v_res_935_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_fromClass_boxed_934_ = (crate::leanh::lean_unbox(v_fromClass_933_) as u8);
    v_res_935_ = l_Lean_addAuxParentProjectionInfo(
        v_env_930_,
        v_projName_931_,
        v_numParams_932_,
        v_fromClass_boxed_934_,
    );
    return v_res_935_;
}
pub unsafe fn l_Lean_Environment_getAuxParentProjectionInfo_x3f(
    mut v_env_936_: *mut crate::leanh::LeanObject,
    mut v_projName_937_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_938_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toEnvExtension_939_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_asyncMode_940_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_941_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_942_: u8 = 0;
    let mut v___x_943_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_938_ = l_Lean_auxParentProjInfoExt;
    v_toEnvExtension_939_ = crate::leanh::lean_ctor_get(v___x_938_, 0);
    v_asyncMode_940_ = crate::leanh::lean_ctor_get(v_toEnvExtension_939_, 2);
    v___x_941_ = l_Lean_instInhabitedAuxParentProjectionInfo_default;
    v___x_942_ = 0;
    v___x_943_ = l_Lean_MapDeclarationExtension_find_x3f___redArg(
        v___x_941_,
        v___x_938_,
        v_env_936_,
        v_projName_937_,
        v_asyncMode_940_,
        v___x_942_,
    );
    return v___x_943_;
}
pub unsafe fn l_Lean_getAuxParentProjectionInfo_x3f___redArg___lam__0(
    mut v_declName_944_: *mut crate::leanh::LeanObject,
    mut v_toPure_945_: *mut crate::leanh::LeanObject,
    mut v_____do__lift_946_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_947_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_948_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_947_ =
        l_Lean_Environment_getAuxParentProjectionInfo_x3f(v_____do__lift_946_, v_declName_944_);
    v___x_948_ = crate::leanh::lean_apply_2(v_toPure_945_, crate::leanh::lean_box(0), v___x_947_);
    return v___x_948_;
}
pub unsafe fn l_Lean_getAuxParentProjectionInfo_x3f___redArg(
    mut v_inst_949_: *mut crate::leanh::LeanObject,
    mut v_inst_950_: *mut crate::leanh::LeanObject,
    mut v_declName_951_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toApplicative_952_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_953_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_getEnv_954_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_955_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_956_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_957_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_952_ = crate::leanh::lean_ctor_get(v_inst_950_, 0);
    crate::leanh::lean_inc_ref(v_toApplicative_952_);
    v_toBind_953_ = crate::leanh::lean_ctor_get(v_inst_950_, 1);
    crate::leanh::lean_inc(v_toBind_953_);
    crate::leanh::lean_dec_ref(v_inst_950_);
    v_getEnv_954_ = crate::leanh::lean_ctor_get(v_inst_949_, 0);
    crate::leanh::lean_inc(v_getEnv_954_);
    crate::leanh::lean_dec_ref(v_inst_949_);
    v_toPure_955_ = crate::leanh::lean_ctor_get(v_toApplicative_952_, 1);
    crate::leanh::lean_inc(v_toPure_955_);
    crate::leanh::lean_dec_ref(v_toApplicative_952_);
    v___f_956_ = crate::leanh::lean_alloc_closure(
        l_Lean_getAuxParentProjectionInfo_x3f___redArg___lam__0 as *mut core::ffi::c_void,
        3,
        2,
    );
    crate::leanh::lean_closure_set(v___f_956_, 0, v_declName_951_);
    crate::leanh::lean_closure_set(v___f_956_, 1, v_toPure_955_);
    v___x_957_ = crate::leanh::lean_apply_4(
        v_toBind_953_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v_getEnv_954_,
        v___f_956_,
    );
    return v___x_957_;
}
pub unsafe fn l_Lean_getAuxParentProjectionInfo_x3f(
    mut v_m_958_: *mut crate::leanh::LeanObject,
    mut v_inst_959_: *mut crate::leanh::LeanObject,
    mut v_inst_960_: *mut crate::leanh::LeanObject,
    mut v_declName_961_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_962_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_962_ =
        l_Lean_getAuxParentProjectionInfo_x3f___redArg(v_inst_959_, v_inst_960_, v_declName_961_);
    return v___x_962_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_ProjFns(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_EnvExtension(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res =
        l___private_Lean_ProjFns_0__Lean_initFn_00___x40_Lean_ProjFns_2268652983____hygCtx___hyg_2_(
        );
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    l_Lean_projectionFnInfoExt = crate::leanh::lean_io_result_get_value(res);
    crate::leanh::lean_mark_persistent(l_Lean_projectionFnInfoExt);
    crate::leanh::lean_dec_ref(res);
    res =
        l___private_Lean_ProjFns_0__Lean_initFn_00___x40_Lean_ProjFns_496916995____hygCtx___hyg_2_(
        );
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    l_Lean_auxParentProjInfoExt = crate::leanh::lean_io_result_get_value(res);
    crate::leanh::lean_mark_persistent(l_Lean_auxParentProjInfoExt);
    crate::leanh::lean_dec_ref(res);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_ProjFns(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_meta_initialized = true;
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lean_ProjFns(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_EnvExtension(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_ProjFns(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Lean_ProjFns(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Lean_ProjFns(builtin);
}
