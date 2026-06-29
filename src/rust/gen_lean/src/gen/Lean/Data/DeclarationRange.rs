// Lean compiler output
// Module: Lean.Data.DeclarationRange
// Imports: Lean.Data.Position
use crate::ffi::{
    lean_array_push, lean_mk_empty_array_with_capacity, lean_name_eq, lean_nat_dec_eq,
    lean_nat_to_int, lean_string_length,
};
use crate::r#gen::Init::Data::Repr::l_Nat_reprFast;
use crate::r#gen::Init::Meta::Defs::l_Lean_Name_reprPrec;
use crate::r#gen::Lean::Data::Position::{
    initialize_Lean_Data_Position, l_Lean_instDecidableEqPosition_decEq,
    l_Lean_instInhabitedPosition_default, l_Lean_instReprPosition_repr___redArg,
    runtime_initialize_Lean_Data_Position,
};
use crate::r#gen::Lean::Expr::{l_Lean_mkAppN, l_Lean_mkConst, l_Lean_mkNatLit};
static mut l_Lean_instInhabitedDeclarationRange_default___closed__0_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_instInhabitedDeclarationRange_default___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static mut l_Lean_instInhabitedDeclarationRange_default: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static mut l_Lean_instInhabitedDeclarationRange: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_instReprDeclarationRange_repr___redArg___closed__0_value:
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
static mut l_Lean_instReprDeclarationRange_repr___redArg___closed__0:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_instReprDeclarationRange_repr___redArg___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_instReprDeclarationRange_repr___redArg___closed__1_value:
    crate::leanh::LeanStringObject<4> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 4,
    m_capacity: 4,
    m_length: 3,
    m_data: [112, 111, 115, 0],
};
static mut l_Lean_instReprDeclarationRange_repr___redArg___closed__1:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_instReprDeclarationRange_repr___redArg___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_instReprDeclarationRange_repr___redArg___closed__2_value:
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
        core::ptr::addr_of!(l_Lean_instReprDeclarationRange_repr___redArg___closed__1_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_instReprDeclarationRange_repr___redArg___closed__2:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_instReprDeclarationRange_repr___redArg___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_instReprDeclarationRange_repr___redArg___closed__3_value:
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
        core::ptr::addr_of!(l_Lean_instReprDeclarationRange_repr___redArg___closed__2_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_instReprDeclarationRange_repr___redArg___closed__3:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_instReprDeclarationRange_repr___redArg___closed__3_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_instReprDeclarationRange_repr___redArg___closed__4_value:
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
static mut l_Lean_instReprDeclarationRange_repr___redArg___closed__4:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_instReprDeclarationRange_repr___redArg___closed__4_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_instReprDeclarationRange_repr___redArg___closed__5_value:
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
        core::ptr::addr_of!(l_Lean_instReprDeclarationRange_repr___redArg___closed__4_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_instReprDeclarationRange_repr___redArg___closed__5:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_instReprDeclarationRange_repr___redArg___closed__5_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_instReprDeclarationRange_repr___redArg___closed__6_value:
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
        core::ptr::addr_of!(l_Lean_instReprDeclarationRange_repr___redArg___closed__3_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_instReprDeclarationRange_repr___redArg___closed__5_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_instReprDeclarationRange_repr___redArg___closed__6:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_instReprDeclarationRange_repr___redArg___closed__6_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_instReprDeclarationRange_repr___redArg___closed__7_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_instReprDeclarationRange_repr___redArg___closed__7:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_instReprDeclarationRange_repr___redArg___closed__8_value:
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
static mut l_Lean_instReprDeclarationRange_repr___redArg___closed__8:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_instReprDeclarationRange_repr___redArg___closed__8_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_instReprDeclarationRange_repr___redArg___closed__9_value:
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
        core::ptr::addr_of!(l_Lean_instReprDeclarationRange_repr___redArg___closed__8_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_instReprDeclarationRange_repr___redArg___closed__9:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_instReprDeclarationRange_repr___redArg___closed__9_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_instReprDeclarationRange_repr___redArg___closed__10_value:
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
    m_data: [99, 104, 97, 114, 85, 116, 102, 49, 54, 0],
};
static mut l_Lean_instReprDeclarationRange_repr___redArg___closed__10:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_instReprDeclarationRange_repr___redArg___closed__10_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_instReprDeclarationRange_repr___redArg___closed__11_value:
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
        core::ptr::addr_of!(l_Lean_instReprDeclarationRange_repr___redArg___closed__10_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_instReprDeclarationRange_repr___redArg___closed__11:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_instReprDeclarationRange_repr___redArg___closed__11_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_instReprDeclarationRange_repr___redArg___closed__12_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_instReprDeclarationRange_repr___redArg___closed__12:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_instReprDeclarationRange_repr___redArg___closed__13_value:
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
    m_data: [101, 110, 100, 80, 111, 115, 0],
};
static mut l_Lean_instReprDeclarationRange_repr___redArg___closed__13:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_instReprDeclarationRange_repr___redArg___closed__13_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_instReprDeclarationRange_repr___redArg___closed__14_value:
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
        core::ptr::addr_of!(l_Lean_instReprDeclarationRange_repr___redArg___closed__13_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_instReprDeclarationRange_repr___redArg___closed__14:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_instReprDeclarationRange_repr___redArg___closed__14_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_instReprDeclarationRange_repr___redArg___closed__15_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_instReprDeclarationRange_repr___redArg___closed__15:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_instReprDeclarationRange_repr___redArg___closed__16_value:
    crate::leanh::LeanStringObject<13> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 13,
    m_capacity: 13,
    m_length: 12,
    m_data: [101, 110, 100, 67, 104, 97, 114, 85, 116, 102, 49, 54, 0],
};
static mut l_Lean_instReprDeclarationRange_repr___redArg___closed__16:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_instReprDeclarationRange_repr___redArg___closed__16_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_instReprDeclarationRange_repr___redArg___closed__17_value:
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
        core::ptr::addr_of!(l_Lean_instReprDeclarationRange_repr___redArg___closed__16_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_instReprDeclarationRange_repr___redArg___closed__17:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_instReprDeclarationRange_repr___redArg___closed__17_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_instReprDeclarationRange_repr___redArg___closed__18_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_instReprDeclarationRange_repr___redArg___closed__18:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_instReprDeclarationRange_repr___redArg___closed__19_value:
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
static mut l_Lean_instReprDeclarationRange_repr___redArg___closed__19:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_instReprDeclarationRange_repr___redArg___closed__19_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_instReprDeclarationRange_repr___redArg___closed__20_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_instReprDeclarationRange_repr___redArg___closed__20:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_instReprDeclarationRange_repr___redArg___closed__21_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_instReprDeclarationRange_repr___redArg___closed__21:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_instReprDeclarationRange_repr___redArg___closed__22_value:
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
        core::ptr::addr_of!(l_Lean_instReprDeclarationRange_repr___redArg___closed__0_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_instReprDeclarationRange_repr___redArg___closed__22:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_instReprDeclarationRange_repr___redArg___closed__22_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_instReprDeclarationRange_repr___redArg___closed__23_value:
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
        core::ptr::addr_of!(l_Lean_instReprDeclarationRange_repr___redArg___closed__19_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_instReprDeclarationRange_repr___redArg___closed__23:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_instReprDeclarationRange_repr___redArg___closed__23_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_instReprDeclarationRange___closed__0_value: crate::leanh::LeanClosureObject<0> =
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
        m_fun: l_Lean_instReprDeclarationRange_repr___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_instReprDeclarationRange___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_instReprDeclarationRange___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Lean_instReprDeclarationRange: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_instReprDeclarationRange___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_instToExprDeclarationRange___lam__0___closed__0_value:
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
    m_data: [76, 101, 97, 110, 0],
};
static mut l_Lean_instToExprDeclarationRange___lam__0___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_instToExprDeclarationRange___lam__0___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_instToExprDeclarationRange___lam__0___closed__1_value:
    crate::leanh::LeanStringObject<17> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 17,
    m_capacity: 17,
    m_length: 16,
    m_data: [
        68, 101, 99, 108, 97, 114, 97, 116, 105, 111, 110, 82, 97, 110, 103, 101, 0,
    ],
};
static mut l_Lean_instToExprDeclarationRange___lam__0___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_instToExprDeclarationRange___lam__0___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_instToExprDeclarationRange___lam__0___closed__2_value:
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
    m_data: [109, 107, 0],
};
static mut l_Lean_instToExprDeclarationRange___lam__0___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_instToExprDeclarationRange___lam__0___closed__2_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_instToExprDeclarationRange___lam__0___closed__3_value_aux_0:
    crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_instToExprDeclarationRange___lam__0___closed__0_value)
            as *mut crate::leanh::LeanObject,
        11948124481539785030 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_instToExprDeclarationRange___lam__0___closed__3_value_aux_1:
    crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_instToExprDeclarationRange___lam__0___closed__3_value_aux_0)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_instToExprDeclarationRange___lam__0___closed__1_value)
            as *mut crate::leanh::LeanObject,
        9209224823825377344 as *mut crate::leanh::LeanObject,
    ],
};
pub static l_Lean_instToExprDeclarationRange___lam__0___closed__3_value:
    crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_instToExprDeclarationRange___lam__0___closed__3_value_aux_1)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_instToExprDeclarationRange___lam__0___closed__2_value)
            as *mut crate::leanh::LeanObject,
        3831656119348534840 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_instToExprDeclarationRange___lam__0___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_instToExprDeclarationRange___lam__0___closed__3_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_instToExprDeclarationRange___lam__0___closed__4_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_instToExprDeclarationRange___lam__0___closed__4: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_instToExprDeclarationRange___lam__0___closed__5_value:
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
    m_data: [80, 111, 115, 105, 116, 105, 111, 110, 0],
};
static mut l_Lean_instToExprDeclarationRange___lam__0___closed__5: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_instToExprDeclarationRange___lam__0___closed__5_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_instToExprDeclarationRange___lam__0___closed__6_value_aux_0:
    crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_instToExprDeclarationRange___lam__0___closed__0_value)
            as *mut crate::leanh::LeanObject,
        11948124481539785030 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_instToExprDeclarationRange___lam__0___closed__6_value_aux_1:
    crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_instToExprDeclarationRange___lam__0___closed__6_value_aux_0)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_instToExprDeclarationRange___lam__0___closed__5_value)
            as *mut crate::leanh::LeanObject,
        7283224396379583297 as *mut crate::leanh::LeanObject,
    ],
};
pub static l_Lean_instToExprDeclarationRange___lam__0___closed__6_value:
    crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_instToExprDeclarationRange___lam__0___closed__6_value_aux_1)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_instToExprDeclarationRange___lam__0___closed__2_value)
            as *mut crate::leanh::LeanObject,
        11125062533858197709 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_instToExprDeclarationRange___lam__0___closed__6: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_instToExprDeclarationRange___lam__0___closed__6_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_instToExprDeclarationRange___lam__0___closed__7_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_instToExprDeclarationRange___lam__0___closed__7: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_instToExprDeclarationRange___closed__0_value: crate::leanh::LeanClosureObject<0> =
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
        m_fun: l_Lean_instToExprDeclarationRange___lam__0 as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_instToExprDeclarationRange___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_instToExprDeclarationRange___closed__0_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_instToExprDeclarationRange___closed__1_value_aux_0: crate::leanh::LeanCtorObject<3> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_instToExprDeclarationRange___lam__0___closed__0_value)
                as *mut crate::leanh::LeanObject,
            11948124481539785030 as *mut crate::leanh::LeanObject,
        ],
    };
pub static l_Lean_instToExprDeclarationRange___closed__1_value: crate::leanh::LeanCtorObject<3> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_instToExprDeclarationRange___closed__1_value_aux_0)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_instToExprDeclarationRange___lam__0___closed__1_value)
                as *mut crate::leanh::LeanObject,
            9209224823825377344 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_instToExprDeclarationRange___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_instToExprDeclarationRange___closed__1_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_instToExprDeclarationRange___closed__2_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_instToExprDeclarationRange___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_instToExprDeclarationRange___closed__3_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_instToExprDeclarationRange___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static mut l_Lean_instToExprDeclarationRange: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_instInhabitedDeclarationRanges_default___closed__0_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_instInhabitedDeclarationRanges_default___closed__0:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static mut l_Lean_instInhabitedDeclarationRanges_default: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static mut l_Lean_instInhabitedDeclarationRanges: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_instReprDeclarationRanges_repr___redArg___closed__0_value:
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
    m_data: [114, 97, 110, 103, 101, 0],
};
static mut l_Lean_instReprDeclarationRanges_repr___redArg___closed__0:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_instReprDeclarationRanges_repr___redArg___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_instReprDeclarationRanges_repr___redArg___closed__1_value:
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
        core::ptr::addr_of!(l_Lean_instReprDeclarationRanges_repr___redArg___closed__0_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_instReprDeclarationRanges_repr___redArg___closed__1:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_instReprDeclarationRanges_repr___redArg___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_instReprDeclarationRanges_repr___redArg___closed__2_value:
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
        core::ptr::addr_of!(l_Lean_instReprDeclarationRanges_repr___redArg___closed__1_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_instReprDeclarationRanges_repr___redArg___closed__2:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_instReprDeclarationRanges_repr___redArg___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_instReprDeclarationRanges_repr___redArg___closed__3_value:
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
        core::ptr::addr_of!(l_Lean_instReprDeclarationRanges_repr___redArg___closed__2_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_instReprDeclarationRange_repr___redArg___closed__5_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_instReprDeclarationRanges_repr___redArg___closed__3:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_instReprDeclarationRanges_repr___redArg___closed__3_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_instReprDeclarationRanges_repr___redArg___closed__4_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_instReprDeclarationRanges_repr___redArg___closed__4:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_instReprDeclarationRanges_repr___redArg___closed__5_value:
    crate::leanh::LeanStringObject<15> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 15,
    m_capacity: 15,
    m_length: 14,
    m_data: [
        115, 101, 108, 101, 99, 116, 105, 111, 110, 82, 97, 110, 103, 101, 0,
    ],
};
static mut l_Lean_instReprDeclarationRanges_repr___redArg___closed__5:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_instReprDeclarationRanges_repr___redArg___closed__5_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_instReprDeclarationRanges_repr___redArg___closed__6_value:
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
        core::ptr::addr_of!(l_Lean_instReprDeclarationRanges_repr___redArg___closed__5_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_instReprDeclarationRanges_repr___redArg___closed__6:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_instReprDeclarationRanges_repr___redArg___closed__6_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_instReprDeclarationRanges_repr___redArg___closed__7_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_instReprDeclarationRanges_repr___redArg___closed__7:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_instReprDeclarationRanges___closed__0_value: crate::leanh::LeanClosureObject<0> =
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
        m_fun: l_Lean_instReprDeclarationRanges_repr___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_instReprDeclarationRanges___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_instReprDeclarationRanges___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Lean_instReprDeclarationRanges: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_instReprDeclarationRanges___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_instToExprDeclarationRanges___lam__0___closed__0_value:
    crate::leanh::LeanStringObject<18> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 18,
    m_capacity: 18,
    m_length: 17,
    m_data: [
        68, 101, 99, 108, 97, 114, 97, 116, 105, 111, 110, 82, 97, 110, 103, 101, 115, 0,
    ],
};
static mut l_Lean_instToExprDeclarationRanges___lam__0___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_instToExprDeclarationRanges___lam__0___closed__0_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_instToExprDeclarationRanges___lam__0___closed__1_value_aux_0:
    crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_instToExprDeclarationRange___lam__0___closed__0_value)
            as *mut crate::leanh::LeanObject,
        11948124481539785030 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_instToExprDeclarationRanges___lam__0___closed__1_value_aux_1:
    crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_instToExprDeclarationRanges___lam__0___closed__1_value_aux_0)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_instToExprDeclarationRanges___lam__0___closed__0_value)
            as *mut crate::leanh::LeanObject,
        4956747414454776495 as *mut crate::leanh::LeanObject,
    ],
};
pub static l_Lean_instToExprDeclarationRanges___lam__0___closed__1_value:
    crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_instToExprDeclarationRanges___lam__0___closed__1_value_aux_1)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_instToExprDeclarationRange___lam__0___closed__2_value)
            as *mut crate::leanh::LeanObject,
        15960823074304203395 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_instToExprDeclarationRanges___lam__0___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_instToExprDeclarationRanges___lam__0___closed__1_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_instToExprDeclarationRanges___lam__0___closed__2_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_instToExprDeclarationRanges___lam__0___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_instToExprDeclarationRanges___closed__0_value: crate::leanh::LeanClosureObject<
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
    m_fun: l_Lean_instToExprDeclarationRanges___lam__0 as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_instToExprDeclarationRanges___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_instToExprDeclarationRanges___closed__0_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_instToExprDeclarationRanges___closed__1_value_aux_0: crate::leanh::LeanCtorObject<3> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_instToExprDeclarationRange___lam__0___closed__0_value)
                as *mut crate::leanh::LeanObject,
            11948124481539785030 as *mut crate::leanh::LeanObject,
        ],
    };
pub static l_Lean_instToExprDeclarationRanges___closed__1_value: crate::leanh::LeanCtorObject<3> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_instToExprDeclarationRanges___closed__1_value_aux_0)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_instToExprDeclarationRanges___lam__0___closed__0_value)
                as *mut crate::leanh::LeanObject,
            4956747414454776495 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_instToExprDeclarationRanges___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_instToExprDeclarationRanges___closed__1_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_instToExprDeclarationRanges___closed__2_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_instToExprDeclarationRanges___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_instToExprDeclarationRanges___closed__3_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_instToExprDeclarationRanges___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static mut l_Lean_instToExprDeclarationRanges: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_instInhabitedDeclarationLocation_default___closed__0_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_instInhabitedDeclarationLocation_default___closed__0:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static mut l_Lean_instInhabitedDeclarationLocation_default: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static mut l_Lean_instInhabitedDeclarationLocation: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_instReprDeclarationLocation_repr___redArg___closed__0_value:
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
    m_data: [109, 111, 100, 117, 108, 101, 0],
};
static mut l_Lean_instReprDeclarationLocation_repr___redArg___closed__0:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_instReprDeclarationLocation_repr___redArg___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_instReprDeclarationLocation_repr___redArg___closed__1_value:
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
        core::ptr::addr_of!(l_Lean_instReprDeclarationLocation_repr___redArg___closed__0_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_instReprDeclarationLocation_repr___redArg___closed__1:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_instReprDeclarationLocation_repr___redArg___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_instReprDeclarationLocation_repr___redArg___closed__2_value:
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
        core::ptr::addr_of!(l_Lean_instReprDeclarationLocation_repr___redArg___closed__1_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_instReprDeclarationLocation_repr___redArg___closed__2:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_instReprDeclarationLocation_repr___redArg___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_instReprDeclarationLocation_repr___redArg___closed__3_value:
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
        core::ptr::addr_of!(l_Lean_instReprDeclarationLocation_repr___redArg___closed__2_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_instReprDeclarationRange_repr___redArg___closed__5_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_instReprDeclarationLocation_repr___redArg___closed__3:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_instReprDeclarationLocation_repr___redArg___closed__3_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_instReprDeclarationLocation___closed__0_value: crate::leanh::LeanClosureObject<
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
    m_fun: l_Lean_instReprDeclarationLocation_repr___boxed as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_instReprDeclarationLocation___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_instReprDeclarationLocation___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Lean_instReprDeclarationLocation: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_instReprDeclarationLocation___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub unsafe fn _init_l_Lean_instInhabitedDeclarationRange_default___closed__0()
-> *mut crate::leanh::LeanObject {
    let mut v___x_422_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_423_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_424_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_422_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_423_ = l_Lean_instInhabitedPosition_default;
    v___x_424_ = crate::leanh::lean_alloc_ctor(0, 4, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_424_, 0, v___x_423_);
    crate::leanh::lean_ctor_set(v___x_424_, 1, v___x_422_);
    crate::leanh::lean_ctor_set(v___x_424_, 2, v___x_423_);
    crate::leanh::lean_ctor_set(v___x_424_, 3, v___x_422_);
    return v___x_424_;
}
pub unsafe fn _init_l_Lean_instInhabitedDeclarationRange_default() -> *mut crate::leanh::LeanObject
{
    let mut v___x_425_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_425_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_instInhabitedDeclarationRange_default___closed__0),
        core::ptr::addr_of_mut!(l_Lean_instInhabitedDeclarationRange_default___closed__0_once),
        _init_l_Lean_instInhabitedDeclarationRange_default___closed__0,
    );
    return v___x_425_;
}
pub unsafe fn _init_l_Lean_instInhabitedDeclarationRange() -> *mut crate::leanh::LeanObject {
    let mut v___x_426_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_426_ = l_Lean_instInhabitedDeclarationRange_default;
    return v___x_426_;
}
pub unsafe fn l_Lean_instDecidableEqDeclarationRange_decEq(
    mut v_x_427_: *mut crate::leanh::LeanObject,
    mut v_x_428_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v_pos_429_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_charUtf16_430_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_endPos_431_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_endCharUtf16_432_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_pos_433_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_charUtf16_434_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_endPos_435_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_endCharUtf16_436_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_437_: u8 = 0;
    v_pos_429_ = crate::leanh::lean_ctor_get(v_x_427_, 0);
    v_charUtf16_430_ = crate::leanh::lean_ctor_get(v_x_427_, 1);
    v_endPos_431_ = crate::leanh::lean_ctor_get(v_x_427_, 2);
    v_endCharUtf16_432_ = crate::leanh::lean_ctor_get(v_x_427_, 3);
    v_pos_433_ = crate::leanh::lean_ctor_get(v_x_428_, 0);
    v_charUtf16_434_ = crate::leanh::lean_ctor_get(v_x_428_, 1);
    v_endPos_435_ = crate::leanh::lean_ctor_get(v_x_428_, 2);
    v_endCharUtf16_436_ = crate::leanh::lean_ctor_get(v_x_428_, 3);
    v___x_437_ = l_Lean_instDecidableEqPosition_decEq(v_pos_429_, v_pos_433_);
    if v___x_437_ == 0 {
        return v___x_437_;
    } else {
        let mut v___x_438_: u8 = 0;
        v___x_438_ = lean_nat_dec_eq(v_charUtf16_430_, v_charUtf16_434_);
        if v___x_438_ == 0 {
            return v___x_438_;
        } else {
            let mut v___x_439_: u8 = 0;
            v___x_439_ = l_Lean_instDecidableEqPosition_decEq(v_endPos_431_, v_endPos_435_);
            if v___x_439_ == 0 {
                return v___x_439_;
            } else {
                let mut v___x_440_: u8 = 0;
                v___x_440_ = lean_nat_dec_eq(v_endCharUtf16_432_, v_endCharUtf16_436_);
                return v___x_440_;
            }
        }
    }
}
pub unsafe fn l_Lean_instDecidableEqDeclarationRange_decEq___boxed(
    mut v_x_441_: *mut crate::leanh::LeanObject,
    mut v_x_442_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_443_: u8 = 0;
    let mut v_r_444_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_443_ = l_Lean_instDecidableEqDeclarationRange_decEq(v_x_441_, v_x_442_);
    crate::leanh::lean_dec_ref(v_x_442_);
    crate::leanh::lean_dec_ref(v_x_441_);
    v_r_444_ = crate::leanh::lean_box((v_res_443_) as usize);
    return v_r_444_;
}
pub unsafe fn l_Lean_instDecidableEqDeclarationRange(
    mut v_x_445_: *mut crate::leanh::LeanObject,
    mut v_x_446_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_447_: u8 = 0;
    v___x_447_ = l_Lean_instDecidableEqDeclarationRange_decEq(v_x_445_, v_x_446_);
    return v___x_447_;
}
pub unsafe fn l_Lean_instDecidableEqDeclarationRange___boxed(
    mut v_x_448_: *mut crate::leanh::LeanObject,
    mut v_x_449_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_450_: u8 = 0;
    let mut v_r_451_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_450_ = l_Lean_instDecidableEqDeclarationRange(v_x_448_, v_x_449_);
    crate::leanh::lean_dec_ref(v_x_449_);
    crate::leanh::lean_dec_ref(v_x_448_);
    v_r_451_ = crate::leanh::lean_box((v_res_450_) as usize);
    return v_r_451_;
}
pub unsafe fn l_Nat_cast___at___00Lean_instReprDeclarationRange_repr_spec__0(
    mut v_a_452_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_453_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_453_ = lean_nat_to_int(v_a_452_);
    return v___x_453_;
}
pub unsafe fn _init_l_Lean_instReprDeclarationRange_repr___redArg___closed__7()
-> *mut crate::leanh::LeanObject {
    let mut v___x_467_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_468_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_467_ = crate::leanh::lean_unsigned_to_nat(7);
    v___x_468_ = lean_nat_to_int(v___x_467_);
    return v___x_468_;
}
pub unsafe fn _init_l_Lean_instReprDeclarationRange_repr___redArg___closed__12()
-> *mut crate::leanh::LeanObject {
    let mut v___x_475_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_476_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_475_ = crate::leanh::lean_unsigned_to_nat(13);
    v___x_476_ = lean_nat_to_int(v___x_475_);
    return v___x_476_;
}
pub unsafe fn _init_l_Lean_instReprDeclarationRange_repr___redArg___closed__15()
-> *mut crate::leanh::LeanObject {
    let mut v___x_480_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_481_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_480_ = crate::leanh::lean_unsigned_to_nat(10);
    v___x_481_ = lean_nat_to_int(v___x_480_);
    return v___x_481_;
}
pub unsafe fn _init_l_Lean_instReprDeclarationRange_repr___redArg___closed__18()
-> *mut crate::leanh::LeanObject {
    let mut v___x_485_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_486_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_485_ = crate::leanh::lean_unsigned_to_nat(16);
    v___x_486_ = lean_nat_to_int(v___x_485_);
    return v___x_486_;
}
pub unsafe fn _init_l_Lean_instReprDeclarationRange_repr___redArg___closed__20()
-> *mut crate::leanh::LeanObject {
    let mut v___x_488_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_489_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_488_ = l_Lean_instReprDeclarationRange_repr___redArg___closed__0;
    v___x_489_ = lean_string_length(v___x_488_);
    return v___x_489_;
}
pub unsafe fn _init_l_Lean_instReprDeclarationRange_repr___redArg___closed__21()
-> *mut crate::leanh::LeanObject {
    let mut v___x_490_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_491_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_490_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_instReprDeclarationRange_repr___redArg___closed__20),
        core::ptr::addr_of_mut!(l_Lean_instReprDeclarationRange_repr___redArg___closed__20_once),
        _init_l_Lean_instReprDeclarationRange_repr___redArg___closed__20,
    );
    v___x_491_ = lean_nat_to_int(v___x_490_);
    return v___x_491_;
}
pub unsafe fn l_Lean_instReprDeclarationRange_repr___redArg(
    mut v_x_496_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_pos_497_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_charUtf16_498_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_endPos_499_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_endCharUtf16_500_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_501_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_502_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_503_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_504_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_505_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_506_: u8 = 0;
    let mut v___x_507_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_508_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_509_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_510_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_511_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_512_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_513_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_514_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_515_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_516_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_517_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_518_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_519_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_520_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_521_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_522_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_523_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_524_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_525_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_526_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_527_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_528_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_529_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_530_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_531_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_532_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_533_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_534_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_535_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_536_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_537_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_538_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_539_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_540_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_541_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_542_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_543_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_544_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_545_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_546_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_547_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_548_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_549_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_pos_497_ = crate::leanh::lean_ctor_get(v_x_496_, 0);
    crate::leanh::lean_inc_ref(v_pos_497_);
    v_charUtf16_498_ = crate::leanh::lean_ctor_get(v_x_496_, 1);
    crate::leanh::lean_inc(v_charUtf16_498_);
    v_endPos_499_ = crate::leanh::lean_ctor_get(v_x_496_, 2);
    crate::leanh::lean_inc_ref(v_endPos_499_);
    v_endCharUtf16_500_ = crate::leanh::lean_ctor_get(v_x_496_, 3);
    crate::leanh::lean_inc(v_endCharUtf16_500_);
    crate::leanh::lean_dec_ref(v_x_496_);
    v___x_501_ = l_Lean_instReprDeclarationRange_repr___redArg___closed__5;
    v___x_502_ = l_Lean_instReprDeclarationRange_repr___redArg___closed__6;
    v___x_503_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_instReprDeclarationRange_repr___redArg___closed__7),
        core::ptr::addr_of_mut!(l_Lean_instReprDeclarationRange_repr___redArg___closed__7_once),
        _init_l_Lean_instReprDeclarationRange_repr___redArg___closed__7,
    );
    v___x_504_ = l_Lean_instReprPosition_repr___redArg(v_pos_497_);
    v___x_505_ = crate::leanh::lean_alloc_ctor(4, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_505_, 0, v___x_503_);
    crate::leanh::lean_ctor_set(v___x_505_, 1, v___x_504_);
    v___x_506_ = 0;
    v___x_507_ = crate::leanh::lean_alloc_ctor(6, 1, (1) as u32);
    crate::leanh::lean_ctor_set(v___x_507_, 0, v___x_505_);
    crate::leanh::lean_ctor_set_uint8(
        v___x_507_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
        v___x_506_,
    );
    v___x_508_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_508_, 0, v___x_502_);
    crate::leanh::lean_ctor_set(v___x_508_, 1, v___x_507_);
    v___x_509_ = l_Lean_instReprDeclarationRange_repr___redArg___closed__9;
    v___x_510_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_510_, 0, v___x_508_);
    crate::leanh::lean_ctor_set(v___x_510_, 1, v___x_509_);
    v___x_511_ = crate::leanh::lean_box(1);
    v___x_512_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_512_, 0, v___x_510_);
    crate::leanh::lean_ctor_set(v___x_512_, 1, v___x_511_);
    v___x_513_ = l_Lean_instReprDeclarationRange_repr___redArg___closed__11;
    v___x_514_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_514_, 0, v___x_512_);
    crate::leanh::lean_ctor_set(v___x_514_, 1, v___x_513_);
    v___x_515_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_515_, 0, v___x_514_);
    crate::leanh::lean_ctor_set(v___x_515_, 1, v___x_501_);
    v___x_516_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_instReprDeclarationRange_repr___redArg___closed__12),
        core::ptr::addr_of_mut!(l_Lean_instReprDeclarationRange_repr___redArg___closed__12_once),
        _init_l_Lean_instReprDeclarationRange_repr___redArg___closed__12,
    );
    v___x_517_ = l_Nat_reprFast(v_charUtf16_498_);
    v___x_518_ = crate::leanh::lean_alloc_ctor(3, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_518_, 0, v___x_517_);
    v___x_519_ = crate::leanh::lean_alloc_ctor(4, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_519_, 0, v___x_516_);
    crate::leanh::lean_ctor_set(v___x_519_, 1, v___x_518_);
    v___x_520_ = crate::leanh::lean_alloc_ctor(6, 1, (1) as u32);
    crate::leanh::lean_ctor_set(v___x_520_, 0, v___x_519_);
    crate::leanh::lean_ctor_set_uint8(
        v___x_520_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
        v___x_506_,
    );
    v___x_521_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_521_, 0, v___x_515_);
    crate::leanh::lean_ctor_set(v___x_521_, 1, v___x_520_);
    v___x_522_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_522_, 0, v___x_521_);
    crate::leanh::lean_ctor_set(v___x_522_, 1, v___x_509_);
    v___x_523_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_523_, 0, v___x_522_);
    crate::leanh::lean_ctor_set(v___x_523_, 1, v___x_511_);
    v___x_524_ = l_Lean_instReprDeclarationRange_repr___redArg___closed__14;
    v___x_525_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_525_, 0, v___x_523_);
    crate::leanh::lean_ctor_set(v___x_525_, 1, v___x_524_);
    v___x_526_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_526_, 0, v___x_525_);
    crate::leanh::lean_ctor_set(v___x_526_, 1, v___x_501_);
    v___x_527_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_instReprDeclarationRange_repr___redArg___closed__15),
        core::ptr::addr_of_mut!(l_Lean_instReprDeclarationRange_repr___redArg___closed__15_once),
        _init_l_Lean_instReprDeclarationRange_repr___redArg___closed__15,
    );
    v___x_528_ = l_Lean_instReprPosition_repr___redArg(v_endPos_499_);
    v___x_529_ = crate::leanh::lean_alloc_ctor(4, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_529_, 0, v___x_527_);
    crate::leanh::lean_ctor_set(v___x_529_, 1, v___x_528_);
    v___x_530_ = crate::leanh::lean_alloc_ctor(6, 1, (1) as u32);
    crate::leanh::lean_ctor_set(v___x_530_, 0, v___x_529_);
    crate::leanh::lean_ctor_set_uint8(
        v___x_530_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
        v___x_506_,
    );
    v___x_531_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_531_, 0, v___x_526_);
    crate::leanh::lean_ctor_set(v___x_531_, 1, v___x_530_);
    v___x_532_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_532_, 0, v___x_531_);
    crate::leanh::lean_ctor_set(v___x_532_, 1, v___x_509_);
    v___x_533_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_533_, 0, v___x_532_);
    crate::leanh::lean_ctor_set(v___x_533_, 1, v___x_511_);
    v___x_534_ = l_Lean_instReprDeclarationRange_repr___redArg___closed__17;
    v___x_535_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_535_, 0, v___x_533_);
    crate::leanh::lean_ctor_set(v___x_535_, 1, v___x_534_);
    v___x_536_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_536_, 0, v___x_535_);
    crate::leanh::lean_ctor_set(v___x_536_, 1, v___x_501_);
    v___x_537_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_instReprDeclarationRange_repr___redArg___closed__18),
        core::ptr::addr_of_mut!(l_Lean_instReprDeclarationRange_repr___redArg___closed__18_once),
        _init_l_Lean_instReprDeclarationRange_repr___redArg___closed__18,
    );
    v___x_538_ = l_Nat_reprFast(v_endCharUtf16_500_);
    v___x_539_ = crate::leanh::lean_alloc_ctor(3, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_539_, 0, v___x_538_);
    v___x_540_ = crate::leanh::lean_alloc_ctor(4, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_540_, 0, v___x_537_);
    crate::leanh::lean_ctor_set(v___x_540_, 1, v___x_539_);
    v___x_541_ = crate::leanh::lean_alloc_ctor(6, 1, (1) as u32);
    crate::leanh::lean_ctor_set(v___x_541_, 0, v___x_540_);
    crate::leanh::lean_ctor_set_uint8(
        v___x_541_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
        v___x_506_,
    );
    v___x_542_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_542_, 0, v___x_536_);
    crate::leanh::lean_ctor_set(v___x_542_, 1, v___x_541_);
    v___x_543_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_instReprDeclarationRange_repr___redArg___closed__21),
        core::ptr::addr_of_mut!(l_Lean_instReprDeclarationRange_repr___redArg___closed__21_once),
        _init_l_Lean_instReprDeclarationRange_repr___redArg___closed__21,
    );
    v___x_544_ = l_Lean_instReprDeclarationRange_repr___redArg___closed__22;
    v___x_545_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_545_, 0, v___x_544_);
    crate::leanh::lean_ctor_set(v___x_545_, 1, v___x_542_);
    v___x_546_ = l_Lean_instReprDeclarationRange_repr___redArg___closed__23;
    v___x_547_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_547_, 0, v___x_545_);
    crate::leanh::lean_ctor_set(v___x_547_, 1, v___x_546_);
    v___x_548_ = crate::leanh::lean_alloc_ctor(4, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_548_, 0, v___x_543_);
    crate::leanh::lean_ctor_set(v___x_548_, 1, v___x_547_);
    v___x_549_ = crate::leanh::lean_alloc_ctor(6, 1, (1) as u32);
    crate::leanh::lean_ctor_set(v___x_549_, 0, v___x_548_);
    crate::leanh::lean_ctor_set_uint8(
        v___x_549_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
        v___x_506_,
    );
    return v___x_549_;
}
pub unsafe fn l_Lean_instReprDeclarationRange_repr(
    mut v_x_550_: *mut crate::leanh::LeanObject,
    mut v_prec_551_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_552_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_552_ = l_Lean_instReprDeclarationRange_repr___redArg(v_x_550_);
    return v___x_552_;
}
pub unsafe fn l_Lean_instReprDeclarationRange_repr___boxed(
    mut v_x_553_: *mut crate::leanh::LeanObject,
    mut v_prec_554_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_555_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_555_ = l_Lean_instReprDeclarationRange_repr(v_x_553_, v_prec_554_);
    crate::leanh::lean_dec(v_prec_554_);
    return v_res_555_;
}
pub unsafe fn _init_l_Lean_instToExprDeclarationRange___lam__0___closed__4()
-> *mut crate::leanh::LeanObject {
    let mut v___x_565_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_566_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_567_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_565_ = crate::leanh::lean_box(0);
    v___x_566_ = l_Lean_instToExprDeclarationRange___lam__0___closed__3;
    v___x_567_ = l_Lean_mkConst(v___x_566_, v___x_565_);
    return v___x_567_;
}
pub unsafe fn _init_l_Lean_instToExprDeclarationRange___lam__0___closed__7()
-> *mut crate::leanh::LeanObject {
    let mut v___x_573_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_574_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_575_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_573_ = crate::leanh::lean_box(0);
    v___x_574_ = l_Lean_instToExprDeclarationRange___lam__0___closed__6;
    v___x_575_ = l_Lean_mkConst(v___x_574_, v___x_573_);
    return v___x_575_;
}
pub unsafe fn l_Lean_instToExprDeclarationRange___lam__0(
    mut v_r_576_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_pos_577_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_endPos_578_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_charUtf16_579_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_endCharUtf16_580_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_line_581_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_column_582_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_line_583_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_column_584_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_585_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_586_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_587_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_588_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_589_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_590_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_591_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_592_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_593_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_594_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_595_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_596_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_597_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_598_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_599_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_600_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_601_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_602_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_603_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_604_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_605_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_606_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_607_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_pos_577_ = crate::leanh::lean_ctor_get(v_r_576_, 0);
    crate::leanh::lean_inc_ref(v_pos_577_);
    v_endPos_578_ = crate::leanh::lean_ctor_get(v_r_576_, 2);
    crate::leanh::lean_inc_ref(v_endPos_578_);
    v_charUtf16_579_ = crate::leanh::lean_ctor_get(v_r_576_, 1);
    crate::leanh::lean_inc(v_charUtf16_579_);
    v_endCharUtf16_580_ = crate::leanh::lean_ctor_get(v_r_576_, 3);
    crate::leanh::lean_inc(v_endCharUtf16_580_);
    crate::leanh::lean_dec_ref(v_r_576_);
    v_line_581_ = crate::leanh::lean_ctor_get(v_pos_577_, 0);
    crate::leanh::lean_inc(v_line_581_);
    v_column_582_ = crate::leanh::lean_ctor_get(v_pos_577_, 1);
    crate::leanh::lean_inc(v_column_582_);
    crate::leanh::lean_dec_ref(v_pos_577_);
    v_line_583_ = crate::leanh::lean_ctor_get(v_endPos_578_, 0);
    crate::leanh::lean_inc(v_line_583_);
    v_column_584_ = crate::leanh::lean_ctor_get(v_endPos_578_, 1);
    crate::leanh::lean_inc(v_column_584_);
    crate::leanh::lean_dec_ref(v_endPos_578_);
    v___x_585_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_instToExprDeclarationRange___lam__0___closed__4),
        core::ptr::addr_of_mut!(l_Lean_instToExprDeclarationRange___lam__0___closed__4_once),
        _init_l_Lean_instToExprDeclarationRange___lam__0___closed__4,
    );
    v___x_586_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_instToExprDeclarationRange___lam__0___closed__7),
        core::ptr::addr_of_mut!(l_Lean_instToExprDeclarationRange___lam__0___closed__7_once),
        _init_l_Lean_instToExprDeclarationRange___lam__0___closed__7,
    );
    v___x_587_ = l_Lean_mkNatLit(v_line_581_);
    v___x_588_ = l_Lean_mkNatLit(v_column_582_);
    v___x_589_ = crate::leanh::lean_unsigned_to_nat(2);
    v___x_590_ = lean_mk_empty_array_with_capacity(v___x_589_);
    crate::leanh::lean_inc_ref(v___x_590_);
    v___x_591_ = lean_array_push(v___x_590_, v___x_587_);
    v___x_592_ = lean_array_push(v___x_591_, v___x_588_);
    v___x_593_ = l_Lean_mkAppN(v___x_586_, v___x_592_);
    crate::leanh::lean_dec_ref(v___x_592_);
    v___x_594_ = l_Lean_mkNatLit(v_charUtf16_579_);
    v___x_595_ = l_Lean_mkNatLit(v_line_583_);
    v___x_596_ = l_Lean_mkNatLit(v_column_584_);
    v___x_597_ = lean_array_push(v___x_590_, v___x_595_);
    v___x_598_ = lean_array_push(v___x_597_, v___x_596_);
    v___x_599_ = l_Lean_mkAppN(v___x_586_, v___x_598_);
    crate::leanh::lean_dec_ref(v___x_598_);
    v___x_600_ = l_Lean_mkNatLit(v_endCharUtf16_580_);
    v___x_601_ = crate::leanh::lean_unsigned_to_nat(4);
    v___x_602_ = lean_mk_empty_array_with_capacity(v___x_601_);
    v___x_603_ = lean_array_push(v___x_602_, v___x_593_);
    v___x_604_ = lean_array_push(v___x_603_, v___x_594_);
    v___x_605_ = lean_array_push(v___x_604_, v___x_599_);
    v___x_606_ = lean_array_push(v___x_605_, v___x_600_);
    v___x_607_ = l_Lean_mkAppN(v___x_585_, v___x_606_);
    crate::leanh::lean_dec_ref(v___x_606_);
    return v___x_607_;
}
pub unsafe fn _init_l_Lean_instToExprDeclarationRange___closed__2() -> *mut crate::leanh::LeanObject
{
    let mut v___x_612_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_613_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_614_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_612_ = crate::leanh::lean_box(0);
    v___x_613_ = l_Lean_instToExprDeclarationRange___closed__1;
    v___x_614_ = l_Lean_mkConst(v___x_613_, v___x_612_);
    return v___x_614_;
}
pub unsafe fn _init_l_Lean_instToExprDeclarationRange___closed__3() -> *mut crate::leanh::LeanObject
{
    let mut v___x_615_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_616_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_617_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_615_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_instToExprDeclarationRange___closed__2),
        core::ptr::addr_of_mut!(l_Lean_instToExprDeclarationRange___closed__2_once),
        _init_l_Lean_instToExprDeclarationRange___closed__2,
    );
    v___f_616_ = l_Lean_instToExprDeclarationRange___closed__0;
    v___x_617_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_617_, 0, v___f_616_);
    crate::leanh::lean_ctor_set(v___x_617_, 1, v___x_615_);
    return v___x_617_;
}
pub unsafe fn _init_l_Lean_instToExprDeclarationRange() -> *mut crate::leanh::LeanObject {
    let mut v___x_618_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_618_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_instToExprDeclarationRange___closed__3),
        core::ptr::addr_of_mut!(l_Lean_instToExprDeclarationRange___closed__3_once),
        _init_l_Lean_instToExprDeclarationRange___closed__3,
    );
    return v___x_618_;
}
pub unsafe fn _init_l_Lean_instInhabitedDeclarationRanges_default___closed__0()
-> *mut crate::leanh::LeanObject {
    let mut v___x_619_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_620_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_619_ = l_Lean_instInhabitedDeclarationRange_default;
    v___x_620_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_620_, 0, v___x_619_);
    crate::leanh::lean_ctor_set(v___x_620_, 1, v___x_619_);
    return v___x_620_;
}
pub unsafe fn _init_l_Lean_instInhabitedDeclarationRanges_default() -> *mut crate::leanh::LeanObject
{
    let mut v___x_621_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_621_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_instInhabitedDeclarationRanges_default___closed__0),
        core::ptr::addr_of_mut!(l_Lean_instInhabitedDeclarationRanges_default___closed__0_once),
        _init_l_Lean_instInhabitedDeclarationRanges_default___closed__0,
    );
    return v___x_621_;
}
pub unsafe fn _init_l_Lean_instInhabitedDeclarationRanges() -> *mut crate::leanh::LeanObject {
    let mut v___x_622_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_622_ = l_Lean_instInhabitedDeclarationRanges_default;
    return v___x_622_;
}
pub unsafe fn _init_l_Lean_instReprDeclarationRanges_repr___redArg___closed__4()
-> *mut crate::leanh::LeanObject {
    let mut v___x_632_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_633_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_632_ = crate::leanh::lean_unsigned_to_nat(9);
    v___x_633_ = lean_nat_to_int(v___x_632_);
    return v___x_633_;
}
pub unsafe fn _init_l_Lean_instReprDeclarationRanges_repr___redArg___closed__7()
-> *mut crate::leanh::LeanObject {
    let mut v___x_637_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_638_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_637_ = crate::leanh::lean_unsigned_to_nat(18);
    v___x_638_ = lean_nat_to_int(v___x_637_);
    return v___x_638_;
}
pub unsafe fn l_Lean_instReprDeclarationRanges_repr___redArg(
    mut v_x_639_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_range_640_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_selectionRange_641_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_643_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_644_: u8 = 0;
    let mut v___x_645_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_646_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_647_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_648_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_650_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_651_: u8 = 0;
    let mut v___x_652_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_653_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_654_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_655_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_656_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_657_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_658_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_659_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_660_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_661_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_662_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_663_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_664_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_665_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_666_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_667_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_668_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_669_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_670_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_671_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_672_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_673_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_674_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_range_640_ = crate::leanh::lean_ctor_get(v_x_639_, 0);
                v_selectionRange_641_ = crate::leanh::lean_ctor_get(v_x_639_, 1);
                v_isSharedCheck_674_ = (!crate::leanh::lean_is_exclusive(v_x_639_)) as u8;
                if v_isSharedCheck_674_ == 0 {
                    v___x_643_ = v_x_639_;
                    v_isShared_644_ = v_isSharedCheck_674_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_selectionRange_641_);
                    crate::leanh::lean_inc(v_range_640_);
                    crate::leanh::lean_dec(v_x_639_);
                    v___x_643_ = crate::leanh::lean_box(0);
                    v_isShared_644_ = v_isSharedCheck_674_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_645_ = l_Lean_instReprDeclarationRange_repr___redArg___closed__5;
                v___x_646_ = l_Lean_instReprDeclarationRanges_repr___redArg___closed__3;
                v___x_647_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Lean_instReprDeclarationRanges_repr___redArg___closed__4
                    ),
                    core::ptr::addr_of_mut!(
                        l_Lean_instReprDeclarationRanges_repr___redArg___closed__4_once
                    ),
                    _init_l_Lean_instReprDeclarationRanges_repr___redArg___closed__4,
                );
                v___x_648_ = l_Lean_instReprDeclarationRange_repr___redArg(v_range_640_);
                if v_isShared_644_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_643_, 4);
                    crate::leanh::lean_ctor_set(v___x_643_, 1, v___x_648_);
                    crate::leanh::lean_ctor_set(v___x_643_, 0, v___x_647_);
                    v___x_650_ = v___x_643_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_673_ = crate::leanh::lean_alloc_ctor(4, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_673_, 0, v___x_647_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_673_, 1, v___x_648_);
                    v___x_650_ = v_reuseFailAlloc_673_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_651_ = 0;
                v___x_652_ = crate::leanh::lean_alloc_ctor(6, 1, (1) as u32);
                crate::leanh::lean_ctor_set(v___x_652_, 0, v___x_650_);
                crate::leanh::lean_ctor_set_uint8(
                    v___x_652_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                    v___x_651_,
                );
                v___x_653_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_653_, 0, v___x_646_);
                crate::leanh::lean_ctor_set(v___x_653_, 1, v___x_652_);
                v___x_654_ = l_Lean_instReprDeclarationRange_repr___redArg___closed__9;
                v___x_655_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_655_, 0, v___x_653_);
                crate::leanh::lean_ctor_set(v___x_655_, 1, v___x_654_);
                v___x_656_ = crate::leanh::lean_box(1);
                v___x_657_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_657_, 0, v___x_655_);
                crate::leanh::lean_ctor_set(v___x_657_, 1, v___x_656_);
                v___x_658_ = l_Lean_instReprDeclarationRanges_repr___redArg___closed__6;
                v___x_659_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_659_, 0, v___x_657_);
                crate::leanh::lean_ctor_set(v___x_659_, 1, v___x_658_);
                v___x_660_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_660_, 0, v___x_659_);
                crate::leanh::lean_ctor_set(v___x_660_, 1, v___x_645_);
                v___x_661_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Lean_instReprDeclarationRanges_repr___redArg___closed__7
                    ),
                    core::ptr::addr_of_mut!(
                        l_Lean_instReprDeclarationRanges_repr___redArg___closed__7_once
                    ),
                    _init_l_Lean_instReprDeclarationRanges_repr___redArg___closed__7,
                );
                v___x_662_ = l_Lean_instReprDeclarationRange_repr___redArg(v_selectionRange_641_);
                v___x_663_ = crate::leanh::lean_alloc_ctor(4, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_663_, 0, v___x_661_);
                crate::leanh::lean_ctor_set(v___x_663_, 1, v___x_662_);
                v___x_664_ = crate::leanh::lean_alloc_ctor(6, 1, (1) as u32);
                crate::leanh::lean_ctor_set(v___x_664_, 0, v___x_663_);
                crate::leanh::lean_ctor_set_uint8(
                    v___x_664_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                    v___x_651_,
                );
                v___x_665_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_665_, 0, v___x_660_);
                crate::leanh::lean_ctor_set(v___x_665_, 1, v___x_664_);
                v___x_666_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Lean_instReprDeclarationRange_repr___redArg___closed__21
                    ),
                    core::ptr::addr_of_mut!(
                        l_Lean_instReprDeclarationRange_repr___redArg___closed__21_once
                    ),
                    _init_l_Lean_instReprDeclarationRange_repr___redArg___closed__21,
                );
                v___x_667_ = l_Lean_instReprDeclarationRange_repr___redArg___closed__22;
                v___x_668_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_668_, 0, v___x_667_);
                crate::leanh::lean_ctor_set(v___x_668_, 1, v___x_665_);
                v___x_669_ = l_Lean_instReprDeclarationRange_repr___redArg___closed__23;
                v___x_670_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_670_, 0, v___x_668_);
                crate::leanh::lean_ctor_set(v___x_670_, 1, v___x_669_);
                v___x_671_ = crate::leanh::lean_alloc_ctor(4, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_671_, 0, v___x_666_);
                crate::leanh::lean_ctor_set(v___x_671_, 1, v___x_670_);
                v___x_672_ = crate::leanh::lean_alloc_ctor(6, 1, (1) as u32);
                crate::leanh::lean_ctor_set(v___x_672_, 0, v___x_671_);
                crate::leanh::lean_ctor_set_uint8(
                    v___x_672_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                    v___x_651_,
                );
                return v___x_672_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_instReprDeclarationRanges_repr(
    mut v_x_675_: *mut crate::leanh::LeanObject,
    mut v_prec_676_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_677_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_677_ = l_Lean_instReprDeclarationRanges_repr___redArg(v_x_675_);
    return v___x_677_;
}
pub unsafe fn l_Lean_instReprDeclarationRanges_repr___boxed(
    mut v_x_678_: *mut crate::leanh::LeanObject,
    mut v_prec_679_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_680_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_680_ = l_Lean_instReprDeclarationRanges_repr(v_x_678_, v_prec_679_);
    crate::leanh::lean_dec(v_prec_679_);
    return v_res_680_;
}
pub unsafe fn _init_l_Lean_instToExprDeclarationRanges___lam__0___closed__2()
-> *mut crate::leanh::LeanObject {
    let mut v___x_688_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_689_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_690_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_688_ = crate::leanh::lean_box(0);
    v___x_689_ = l_Lean_instToExprDeclarationRanges___lam__0___closed__1;
    v___x_690_ = l_Lean_mkConst(v___x_689_, v___x_688_);
    return v___x_690_;
}
pub unsafe fn l_Lean_instToExprDeclarationRanges___lam__0(
    mut v_r_691_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_range_692_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_selectionRange_693_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_pos_694_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_charUtf16_695_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_endPos_696_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_endCharUtf16_697_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_698_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_line_699_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_column_700_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_line_701_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_column_702_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_703_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_pos_704_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_charUtf16_705_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_endPos_706_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_endCharUtf16_707_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_line_708_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_column_709_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_710_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_711_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_712_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_713_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_714_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_715_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_716_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_717_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_line_718_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_column_719_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_720_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_721_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_722_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_723_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_724_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_725_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_726_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_727_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_728_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_729_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_730_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_731_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_732_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_733_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_734_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_735_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_736_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_737_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_738_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_739_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_740_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_741_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_742_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_743_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_744_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_745_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_746_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_747_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_748_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_749_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_750_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_751_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_752_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_753_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_range_692_ = crate::leanh::lean_ctor_get(v_r_691_, 0);
    crate::leanh::lean_inc_ref(v_range_692_);
    v_selectionRange_693_ = crate::leanh::lean_ctor_get(v_r_691_, 1);
    crate::leanh::lean_inc_ref(v_selectionRange_693_);
    crate::leanh::lean_dec_ref(v_r_691_);
    v_pos_694_ = crate::leanh::lean_ctor_get(v_range_692_, 0);
    crate::leanh::lean_inc_ref(v_pos_694_);
    v_charUtf16_695_ = crate::leanh::lean_ctor_get(v_range_692_, 1);
    crate::leanh::lean_inc(v_charUtf16_695_);
    v_endPos_696_ = crate::leanh::lean_ctor_get(v_range_692_, 2);
    crate::leanh::lean_inc_ref(v_endPos_696_);
    v_endCharUtf16_697_ = crate::leanh::lean_ctor_get(v_range_692_, 3);
    crate::leanh::lean_inc(v_endCharUtf16_697_);
    crate::leanh::lean_dec_ref(v_range_692_);
    v___x_698_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_instToExprDeclarationRanges___lam__0___closed__2),
        core::ptr::addr_of_mut!(l_Lean_instToExprDeclarationRanges___lam__0___closed__2_once),
        _init_l_Lean_instToExprDeclarationRanges___lam__0___closed__2,
    );
    v_line_699_ = crate::leanh::lean_ctor_get(v_pos_694_, 0);
    crate::leanh::lean_inc(v_line_699_);
    v_column_700_ = crate::leanh::lean_ctor_get(v_pos_694_, 1);
    crate::leanh::lean_inc(v_column_700_);
    crate::leanh::lean_dec_ref(v_pos_694_);
    v_line_701_ = crate::leanh::lean_ctor_get(v_endPos_696_, 0);
    crate::leanh::lean_inc(v_line_701_);
    v_column_702_ = crate::leanh::lean_ctor_get(v_endPos_696_, 1);
    crate::leanh::lean_inc(v_column_702_);
    crate::leanh::lean_dec_ref(v_endPos_696_);
    v___x_703_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_instToExprDeclarationRange___lam__0___closed__4),
        core::ptr::addr_of_mut!(l_Lean_instToExprDeclarationRange___lam__0___closed__4_once),
        _init_l_Lean_instToExprDeclarationRange___lam__0___closed__4,
    );
    v_pos_704_ = crate::leanh::lean_ctor_get(v_selectionRange_693_, 0);
    crate::leanh::lean_inc_ref(v_pos_704_);
    v_charUtf16_705_ = crate::leanh::lean_ctor_get(v_selectionRange_693_, 1);
    crate::leanh::lean_inc(v_charUtf16_705_);
    v_endPos_706_ = crate::leanh::lean_ctor_get(v_selectionRange_693_, 2);
    crate::leanh::lean_inc_ref(v_endPos_706_);
    v_endCharUtf16_707_ = crate::leanh::lean_ctor_get(v_selectionRange_693_, 3);
    crate::leanh::lean_inc(v_endCharUtf16_707_);
    crate::leanh::lean_dec_ref(v_selectionRange_693_);
    v_line_708_ = crate::leanh::lean_ctor_get(v_pos_704_, 0);
    crate::leanh::lean_inc(v_line_708_);
    v_column_709_ = crate::leanh::lean_ctor_get(v_pos_704_, 1);
    crate::leanh::lean_inc(v_column_709_);
    crate::leanh::lean_dec_ref(v_pos_704_);
    v___x_710_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_instToExprDeclarationRange___lam__0___closed__7),
        core::ptr::addr_of_mut!(l_Lean_instToExprDeclarationRange___lam__0___closed__7_once),
        _init_l_Lean_instToExprDeclarationRange___lam__0___closed__7,
    );
    v___x_711_ = l_Lean_mkNatLit(v_line_699_);
    v___x_712_ = l_Lean_mkNatLit(v_column_700_);
    v___x_713_ = crate::leanh::lean_unsigned_to_nat(2);
    v___x_714_ = lean_mk_empty_array_with_capacity(v___x_713_);
    crate::leanh::lean_inc_ref_n(v___x_714_, 4);
    v___x_715_ = lean_array_push(v___x_714_, v___x_711_);
    v___x_716_ = lean_array_push(v___x_715_, v___x_712_);
    v___x_717_ = l_Lean_mkAppN(v___x_710_, v___x_716_);
    crate::leanh::lean_dec_ref(v___x_716_);
    v_line_718_ = crate::leanh::lean_ctor_get(v_endPos_706_, 0);
    crate::leanh::lean_inc(v_line_718_);
    v_column_719_ = crate::leanh::lean_ctor_get(v_endPos_706_, 1);
    crate::leanh::lean_inc(v_column_719_);
    crate::leanh::lean_dec_ref(v_endPos_706_);
    v___x_720_ = l_Lean_mkNatLit(v_line_701_);
    v___x_721_ = l_Lean_mkNatLit(v_column_702_);
    v___x_722_ = lean_array_push(v___x_714_, v___x_720_);
    v___x_723_ = lean_array_push(v___x_722_, v___x_721_);
    v___x_724_ = l_Lean_mkAppN(v___x_710_, v___x_723_);
    crate::leanh::lean_dec_ref(v___x_723_);
    v___x_725_ = l_Lean_mkNatLit(v_charUtf16_695_);
    v___x_726_ = l_Lean_mkNatLit(v_endCharUtf16_697_);
    v___x_727_ = crate::leanh::lean_unsigned_to_nat(4);
    v___x_728_ = lean_mk_empty_array_with_capacity(v___x_727_);
    crate::leanh::lean_inc_ref(v___x_728_);
    v___x_729_ = lean_array_push(v___x_728_, v___x_717_);
    v___x_730_ = lean_array_push(v___x_729_, v___x_725_);
    v___x_731_ = lean_array_push(v___x_730_, v___x_724_);
    v___x_732_ = lean_array_push(v___x_731_, v___x_726_);
    v___x_733_ = l_Lean_mkAppN(v___x_703_, v___x_732_);
    crate::leanh::lean_dec_ref(v___x_732_);
    v___x_734_ = l_Lean_mkNatLit(v_line_708_);
    v___x_735_ = l_Lean_mkNatLit(v_column_709_);
    v___x_736_ = lean_array_push(v___x_714_, v___x_734_);
    v___x_737_ = lean_array_push(v___x_736_, v___x_735_);
    v___x_738_ = l_Lean_mkAppN(v___x_710_, v___x_737_);
    crate::leanh::lean_dec_ref(v___x_737_);
    v___x_739_ = l_Lean_mkNatLit(v_charUtf16_705_);
    v___x_740_ = l_Lean_mkNatLit(v_line_718_);
    v___x_741_ = l_Lean_mkNatLit(v_column_719_);
    v___x_742_ = lean_array_push(v___x_714_, v___x_740_);
    v___x_743_ = lean_array_push(v___x_742_, v___x_741_);
    v___x_744_ = l_Lean_mkAppN(v___x_710_, v___x_743_);
    crate::leanh::lean_dec_ref(v___x_743_);
    v___x_745_ = l_Lean_mkNatLit(v_endCharUtf16_707_);
    v___x_746_ = lean_array_push(v___x_728_, v___x_738_);
    v___x_747_ = lean_array_push(v___x_746_, v___x_739_);
    v___x_748_ = lean_array_push(v___x_747_, v___x_744_);
    v___x_749_ = lean_array_push(v___x_748_, v___x_745_);
    v___x_750_ = l_Lean_mkAppN(v___x_703_, v___x_749_);
    crate::leanh::lean_dec_ref(v___x_749_);
    v___x_751_ = lean_array_push(v___x_714_, v___x_733_);
    v___x_752_ = lean_array_push(v___x_751_, v___x_750_);
    v___x_753_ = l_Lean_mkAppN(v___x_698_, v___x_752_);
    crate::leanh::lean_dec_ref(v___x_752_);
    return v___x_753_;
}
pub unsafe fn _init_l_Lean_instToExprDeclarationRanges___closed__2() -> *mut crate::leanh::LeanObject
{
    let mut v___x_758_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_759_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_760_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_758_ = crate::leanh::lean_box(0);
    v___x_759_ = l_Lean_instToExprDeclarationRanges___closed__1;
    v___x_760_ = l_Lean_mkConst(v___x_759_, v___x_758_);
    return v___x_760_;
}
pub unsafe fn _init_l_Lean_instToExprDeclarationRanges___closed__3() -> *mut crate::leanh::LeanObject
{
    let mut v___x_761_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_762_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_763_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_761_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_instToExprDeclarationRanges___closed__2),
        core::ptr::addr_of_mut!(l_Lean_instToExprDeclarationRanges___closed__2_once),
        _init_l_Lean_instToExprDeclarationRanges___closed__2,
    );
    v___f_762_ = l_Lean_instToExprDeclarationRanges___closed__0;
    v___x_763_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_763_, 0, v___f_762_);
    crate::leanh::lean_ctor_set(v___x_763_, 1, v___x_761_);
    return v___x_763_;
}
pub unsafe fn _init_l_Lean_instToExprDeclarationRanges() -> *mut crate::leanh::LeanObject {
    let mut v___x_764_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_764_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_instToExprDeclarationRanges___closed__3),
        core::ptr::addr_of_mut!(l_Lean_instToExprDeclarationRanges___closed__3_once),
        _init_l_Lean_instToExprDeclarationRanges___closed__3,
    );
    return v___x_764_;
}
pub unsafe fn _init_l_Lean_instInhabitedDeclarationLocation_default___closed__0()
-> *mut crate::leanh::LeanObject {
    let mut v___x_765_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_766_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_767_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_765_ = l_Lean_instInhabitedDeclarationRange_default;
    v___x_766_ = crate::leanh::lean_box(0);
    v___x_767_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_767_, 0, v___x_766_);
    crate::leanh::lean_ctor_set(v___x_767_, 1, v___x_765_);
    return v___x_767_;
}
pub unsafe fn _init_l_Lean_instInhabitedDeclarationLocation_default()
-> *mut crate::leanh::LeanObject {
    let mut v___x_768_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_768_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_instInhabitedDeclarationLocation_default___closed__0),
        core::ptr::addr_of_mut!(l_Lean_instInhabitedDeclarationLocation_default___closed__0_once),
        _init_l_Lean_instInhabitedDeclarationLocation_default___closed__0,
    );
    return v___x_768_;
}
pub unsafe fn _init_l_Lean_instInhabitedDeclarationLocation() -> *mut crate::leanh::LeanObject {
    let mut v___x_769_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_769_ = l_Lean_instInhabitedDeclarationLocation_default;
    return v___x_769_;
}
pub unsafe fn l_Lean_instDecidableEqDeclarationLocation_decEq(
    mut v_x_770_: *mut crate::leanh::LeanObject,
    mut v_x_771_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v_module_772_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_range_773_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_module_774_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_range_775_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_776_: u8 = 0;
    v_module_772_ = crate::leanh::lean_ctor_get(v_x_770_, 0);
    v_range_773_ = crate::leanh::lean_ctor_get(v_x_770_, 1);
    v_module_774_ = crate::leanh::lean_ctor_get(v_x_771_, 0);
    v_range_775_ = crate::leanh::lean_ctor_get(v_x_771_, 1);
    v___x_776_ = lean_name_eq(v_module_772_, v_module_774_);
    if v___x_776_ == 0 {
        return v___x_776_;
    } else {
        let mut v___x_777_: u8 = 0;
        v___x_777_ = l_Lean_instDecidableEqDeclarationRange_decEq(v_range_773_, v_range_775_);
        return v___x_777_;
    }
}
pub unsafe fn l_Lean_instDecidableEqDeclarationLocation_decEq___boxed(
    mut v_x_778_: *mut crate::leanh::LeanObject,
    mut v_x_779_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_780_: u8 = 0;
    let mut v_r_781_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_780_ = l_Lean_instDecidableEqDeclarationLocation_decEq(v_x_778_, v_x_779_);
    crate::leanh::lean_dec_ref(v_x_779_);
    crate::leanh::lean_dec_ref(v_x_778_);
    v_r_781_ = crate::leanh::lean_box((v_res_780_) as usize);
    return v_r_781_;
}
pub unsafe fn l_Lean_instDecidableEqDeclarationLocation(
    mut v_x_782_: *mut crate::leanh::LeanObject,
    mut v_x_783_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_784_: u8 = 0;
    v___x_784_ = l_Lean_instDecidableEqDeclarationLocation_decEq(v_x_782_, v_x_783_);
    return v___x_784_;
}
pub unsafe fn l_Lean_instDecidableEqDeclarationLocation___boxed(
    mut v_x_785_: *mut crate::leanh::LeanObject,
    mut v_x_786_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_787_: u8 = 0;
    let mut v_r_788_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_787_ = l_Lean_instDecidableEqDeclarationLocation(v_x_785_, v_x_786_);
    crate::leanh::lean_dec_ref(v_x_786_);
    crate::leanh::lean_dec_ref(v_x_785_);
    v_r_788_ = crate::leanh::lean_box((v_res_787_) as usize);
    return v_r_788_;
}
pub unsafe fn l_Lean_instReprDeclarationLocation_repr___redArg(
    mut v_x_798_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_module_799_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_range_800_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_802_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_803_: u8 = 0;
    let mut v___x_804_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_805_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_806_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_807_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_808_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_810_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_811_: u8 = 0;
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
    let mut v___x_831_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_832_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_833_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_834_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_module_799_ = crate::leanh::lean_ctor_get(v_x_798_, 0);
                v_range_800_ = crate::leanh::lean_ctor_get(v_x_798_, 1);
                v_isSharedCheck_834_ = (!crate::leanh::lean_is_exclusive(v_x_798_)) as u8;
                if v_isSharedCheck_834_ == 0 {
                    v___x_802_ = v_x_798_;
                    v_isShared_803_ = v_isSharedCheck_834_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_range_800_);
                    crate::leanh::lean_inc(v_module_799_);
                    crate::leanh::lean_dec(v_x_798_);
                    v___x_802_ = crate::leanh::lean_box(0);
                    v_isShared_803_ = v_isSharedCheck_834_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_804_ = l_Lean_instReprDeclarationRange_repr___redArg___closed__5;
                v___x_805_ = l_Lean_instReprDeclarationLocation_repr___redArg___closed__3;
                v___x_806_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Lean_instReprDeclarationRange_repr___redArg___closed__15
                    ),
                    core::ptr::addr_of_mut!(
                        l_Lean_instReprDeclarationRange_repr___redArg___closed__15_once
                    ),
                    _init_l_Lean_instReprDeclarationRange_repr___redArg___closed__15,
                );
                v___x_807_ = crate::leanh::lean_unsigned_to_nat(0);
                v___x_808_ = l_Lean_Name_reprPrec(v_module_799_, v___x_807_);
                if v_isShared_803_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_802_, 4);
                    crate::leanh::lean_ctor_set(v___x_802_, 1, v___x_808_);
                    crate::leanh::lean_ctor_set(v___x_802_, 0, v___x_806_);
                    v___x_810_ = v___x_802_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_833_ = crate::leanh::lean_alloc_ctor(4, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_833_, 0, v___x_806_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_833_, 1, v___x_808_);
                    v___x_810_ = v_reuseFailAlloc_833_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_811_ = 0;
                v___x_812_ = crate::leanh::lean_alloc_ctor(6, 1, (1) as u32);
                crate::leanh::lean_ctor_set(v___x_812_, 0, v___x_810_);
                crate::leanh::lean_ctor_set_uint8(
                    v___x_812_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                    v___x_811_,
                );
                v___x_813_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_813_, 0, v___x_805_);
                crate::leanh::lean_ctor_set(v___x_813_, 1, v___x_812_);
                v___x_814_ = l_Lean_instReprDeclarationRange_repr___redArg___closed__9;
                v___x_815_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_815_, 0, v___x_813_);
                crate::leanh::lean_ctor_set(v___x_815_, 1, v___x_814_);
                v___x_816_ = crate::leanh::lean_box(1);
                v___x_817_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_817_, 0, v___x_815_);
                crate::leanh::lean_ctor_set(v___x_817_, 1, v___x_816_);
                v___x_818_ = l_Lean_instReprDeclarationRanges_repr___redArg___closed__1;
                v___x_819_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_819_, 0, v___x_817_);
                crate::leanh::lean_ctor_set(v___x_819_, 1, v___x_818_);
                v___x_820_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_820_, 0, v___x_819_);
                crate::leanh::lean_ctor_set(v___x_820_, 1, v___x_804_);
                v___x_821_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Lean_instReprDeclarationRanges_repr___redArg___closed__4
                    ),
                    core::ptr::addr_of_mut!(
                        l_Lean_instReprDeclarationRanges_repr___redArg___closed__4_once
                    ),
                    _init_l_Lean_instReprDeclarationRanges_repr___redArg___closed__4,
                );
                v___x_822_ = l_Lean_instReprDeclarationRange_repr___redArg(v_range_800_);
                v___x_823_ = crate::leanh::lean_alloc_ctor(4, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_823_, 0, v___x_821_);
                crate::leanh::lean_ctor_set(v___x_823_, 1, v___x_822_);
                v___x_824_ = crate::leanh::lean_alloc_ctor(6, 1, (1) as u32);
                crate::leanh::lean_ctor_set(v___x_824_, 0, v___x_823_);
                crate::leanh::lean_ctor_set_uint8(
                    v___x_824_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                    v___x_811_,
                );
                v___x_825_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_825_, 0, v___x_820_);
                crate::leanh::lean_ctor_set(v___x_825_, 1, v___x_824_);
                v___x_826_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Lean_instReprDeclarationRange_repr___redArg___closed__21
                    ),
                    core::ptr::addr_of_mut!(
                        l_Lean_instReprDeclarationRange_repr___redArg___closed__21_once
                    ),
                    _init_l_Lean_instReprDeclarationRange_repr___redArg___closed__21,
                );
                v___x_827_ = l_Lean_instReprDeclarationRange_repr___redArg___closed__22;
                v___x_828_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_828_, 0, v___x_827_);
                crate::leanh::lean_ctor_set(v___x_828_, 1, v___x_825_);
                v___x_829_ = l_Lean_instReprDeclarationRange_repr___redArg___closed__23;
                v___x_830_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_830_, 0, v___x_828_);
                crate::leanh::lean_ctor_set(v___x_830_, 1, v___x_829_);
                v___x_831_ = crate::leanh::lean_alloc_ctor(4, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_831_, 0, v___x_826_);
                crate::leanh::lean_ctor_set(v___x_831_, 1, v___x_830_);
                v___x_832_ = crate::leanh::lean_alloc_ctor(6, 1, (1) as u32);
                crate::leanh::lean_ctor_set(v___x_832_, 0, v___x_831_);
                crate::leanh::lean_ctor_set_uint8(
                    v___x_832_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                    v___x_811_,
                );
                return v___x_832_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_instReprDeclarationLocation_repr(
    mut v_x_835_: *mut crate::leanh::LeanObject,
    mut v_prec_836_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_837_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_837_ = l_Lean_instReprDeclarationLocation_repr___redArg(v_x_835_);
    return v___x_837_;
}
pub unsafe fn l_Lean_instReprDeclarationLocation_repr___boxed(
    mut v_x_838_: *mut crate::leanh::LeanObject,
    mut v_prec_839_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_840_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_840_ = l_Lean_instReprDeclarationLocation_repr(v_x_838_, v_prec_839_);
    crate::leanh::lean_dec(v_prec_839_);
    return v_res_840_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Data_DeclarationRange(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Data_Position(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    l_Lean_instInhabitedDeclarationRange_default =
        _init_l_Lean_instInhabitedDeclarationRange_default();
    crate::leanh::lean_mark_persistent(l_Lean_instInhabitedDeclarationRange_default);
    l_Lean_instInhabitedDeclarationRange = _init_l_Lean_instInhabitedDeclarationRange();
    crate::leanh::lean_mark_persistent(l_Lean_instInhabitedDeclarationRange);
    l_Lean_instToExprDeclarationRange = _init_l_Lean_instToExprDeclarationRange();
    crate::leanh::lean_mark_persistent(l_Lean_instToExprDeclarationRange);
    l_Lean_instInhabitedDeclarationRanges_default =
        _init_l_Lean_instInhabitedDeclarationRanges_default();
    crate::leanh::lean_mark_persistent(l_Lean_instInhabitedDeclarationRanges_default);
    l_Lean_instInhabitedDeclarationRanges = _init_l_Lean_instInhabitedDeclarationRanges();
    crate::leanh::lean_mark_persistent(l_Lean_instInhabitedDeclarationRanges);
    l_Lean_instToExprDeclarationRanges = _init_l_Lean_instToExprDeclarationRanges();
    crate::leanh::lean_mark_persistent(l_Lean_instToExprDeclarationRanges);
    l_Lean_instInhabitedDeclarationLocation_default =
        _init_l_Lean_instInhabitedDeclarationLocation_default();
    crate::leanh::lean_mark_persistent(l_Lean_instInhabitedDeclarationLocation_default);
    l_Lean_instInhabitedDeclarationLocation = _init_l_Lean_instInhabitedDeclarationLocation();
    crate::leanh::lean_mark_persistent(l_Lean_instInhabitedDeclarationLocation);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Data_DeclarationRange(
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
pub unsafe fn initialize_Lean_Data_DeclarationRange(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Data_Position(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Data_DeclarationRange(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Lean_Data_DeclarationRange(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Lean_Data_DeclarationRange(builtin);
}
