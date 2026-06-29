// Lean compiler output
// Module: Std.Internal.Parsec.Basic
// Imports: Init.NotationExtra Init.Data.ToString.Macro Init.Data.Array.Basic
use crate::r#gen::Init::Data::Array::Basic::{
    initialize_Init_Data_Array_Basic, runtime_initialize_Init_Data_Array_Basic,
};
use crate::r#gen::Init::Data::Repr::{l_Repr_addAppParen, l_String_quote};
use crate::r#gen::Init::Data::ToString::Macro::{
    initialize_Init_Data_ToString_Macro, runtime_initialize_Init_Data_ToString_Macro,
};
use crate::r#gen::Init::NotationExtra::{
    initialize_Init_NotationExtra, runtime_initialize_Init_NotationExtra,
};
use crate::ffi::lean_nat_to_int;
use crate::ffi::lean_string_push;
use crate::ffi::{
    lean_array_push, lean_mk_empty_array_with_capacity, lean_nat_dec_le,
};
pub static l_Std_Internal_Parsec_instReprError_repr___closed__0_value:
    crate::leanh::LeanStringObject<30> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 30,
    m_capacity: 30,
    m_length: 29,
    m_data: [
        83, 116, 100, 46, 73, 110, 116, 101, 114, 110, 97, 108, 46, 80, 97, 114, 115, 101, 99, 46,
        69, 114, 114, 111, 114, 46, 101, 111, 102, 0,
    ],
};
static mut l_Std_Internal_Parsec_instReprError_repr___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Internal_Parsec_instReprError_repr___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Internal_Parsec_instReprError_repr___closed__1_value:
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
        core::ptr::addr_of!(l_Std_Internal_Parsec_instReprError_repr___closed__0_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Std_Internal_Parsec_instReprError_repr___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Internal_Parsec_instReprError_repr___closed__1_value)
        as *mut crate::leanh::LeanObject;
static mut l_Std_Internal_Parsec_instReprError_repr___closed__2_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Internal_Parsec_instReprError_repr___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Std_Internal_Parsec_instReprError_repr___closed__3_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Internal_Parsec_instReprError_repr___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Std_Internal_Parsec_instReprError_repr___closed__4_value:
    crate::leanh::LeanStringObject<32> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 32,
    m_capacity: 32,
    m_length: 31,
    m_data: [
        83, 116, 100, 46, 73, 110, 116, 101, 114, 110, 97, 108, 46, 80, 97, 114, 115, 101, 99, 46,
        69, 114, 114, 111, 114, 46, 111, 116, 104, 101, 114, 0,
    ],
};
static mut l_Std_Internal_Parsec_instReprError_repr___closed__4: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Internal_Parsec_instReprError_repr___closed__4_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Internal_Parsec_instReprError_repr___closed__5_value:
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
        core::ptr::addr_of!(l_Std_Internal_Parsec_instReprError_repr___closed__4_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Std_Internal_Parsec_instReprError_repr___closed__5: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Internal_Parsec_instReprError_repr___closed__5_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Internal_Parsec_instReprError_repr___closed__6_value:
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
        core::ptr::addr_of!(l_Std_Internal_Parsec_instReprError_repr___closed__5_value)
            as *mut crate::leanh::LeanObject,
        (((1 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Std_Internal_Parsec_instReprError_repr___closed__6: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Internal_Parsec_instReprError_repr___closed__6_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Internal_Parsec_instReprError___closed__0_value: crate::leanh::LeanClosureObject<
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
    m_fun: l_Std_Internal_Parsec_instReprError_repr___boxed as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Std_Internal_Parsec_instReprError___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Internal_Parsec_instReprError___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Std_Internal_Parsec_instReprError: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Internal_Parsec_instReprError___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Internal_Parsec_instToStringError___lam__0___closed__0_value:
    crate::leanh::LeanStringObject<24> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 24,
    m_capacity: 24,
    m_length: 23,
    m_data: [
        117, 110, 101, 120, 112, 101, 99, 116, 101, 100, 32, 101, 110, 100, 32, 111, 102, 32, 105,
        110, 112, 117, 116, 0,
    ],
};
static mut l_Std_Internal_Parsec_instToStringError___lam__0___closed__0:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Internal_Parsec_instToStringError___lam__0___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Internal_Parsec_instToStringError___closed__0_value:
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
    m_fun: l_Std_Internal_Parsec_instToStringError___lam__0___boxed as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Std_Internal_Parsec_instToStringError___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Internal_Parsec_instToStringError___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Std_Internal_Parsec_instToStringError: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Internal_Parsec_instToStringError___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Internal_Parsec_instReprParseResult_repr___redArg___closed__0_value:
    crate::leanh::LeanStringObject<40> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 40,
    m_capacity: 40,
    m_length: 39,
    m_data: [
        83, 116, 100, 46, 73, 110, 116, 101, 114, 110, 97, 108, 46, 80, 97, 114, 115, 101, 99, 46,
        80, 97, 114, 115, 101, 82, 101, 115, 117, 108, 116, 46, 115, 117, 99, 99, 101, 115, 115, 0,
    ],
};
static mut l_Std_Internal_Parsec_instReprParseResult_repr___redArg___closed__0:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Internal_Parsec_instReprParseResult_repr___redArg___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Internal_Parsec_instReprParseResult_repr___redArg___closed__1_value:
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
        l_Std_Internal_Parsec_instReprParseResult_repr___redArg___closed__0_value
    ) as *mut crate::leanh::LeanObject],
};
static mut l_Std_Internal_Parsec_instReprParseResult_repr___redArg___closed__1:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Internal_Parsec_instReprParseResult_repr___redArg___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Internal_Parsec_instReprParseResult_repr___redArg___closed__2_value:
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
        core::ptr::addr_of!(
            l_Std_Internal_Parsec_instReprParseResult_repr___redArg___closed__1_value
        ) as *mut crate::leanh::LeanObject,
        (((1 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Std_Internal_Parsec_instReprParseResult_repr___redArg___closed__2:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Internal_Parsec_instReprParseResult_repr___redArg___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Internal_Parsec_instReprParseResult_repr___redArg___closed__3_value:
    crate::leanh::LeanStringObject<38> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 38,
    m_capacity: 38,
    m_length: 37,
    m_data: [
        83, 116, 100, 46, 73, 110, 116, 101, 114, 110, 97, 108, 46, 80, 97, 114, 115, 101, 99, 46,
        80, 97, 114, 115, 101, 82, 101, 115, 117, 108, 116, 46, 101, 114, 114, 111, 114, 0,
    ],
};
static mut l_Std_Internal_Parsec_instReprParseResult_repr___redArg___closed__3:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Internal_Parsec_instReprParseResult_repr___redArg___closed__3_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Internal_Parsec_instReprParseResult_repr___redArg___closed__4_value:
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
        l_Std_Internal_Parsec_instReprParseResult_repr___redArg___closed__3_value
    ) as *mut crate::leanh::LeanObject],
};
static mut l_Std_Internal_Parsec_instReprParseResult_repr___redArg___closed__4:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Internal_Parsec_instReprParseResult_repr___redArg___closed__4_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Internal_Parsec_instReprParseResult_repr___redArg___closed__5_value:
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
        core::ptr::addr_of!(
            l_Std_Internal_Parsec_instReprParseResult_repr___redArg___closed__4_value
        ) as *mut crate::leanh::LeanObject,
        (((1 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Std_Internal_Parsec_instReprParseResult_repr___redArg___closed__5:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Internal_Parsec_instReprParseResult_repr___redArg___closed__5_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Internal_Parsec_instInhabited___lam__0___closed__0_value:
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
static mut l_Std_Internal_Parsec_instInhabited___lam__0___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Internal_Parsec_instInhabited___lam__0___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Internal_Parsec_instInhabited___lam__0___closed__1_value:
    crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Std_Internal_Parsec_instInhabited___lam__0___closed__0_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Std_Internal_Parsec_instInhabited___lam__0___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Internal_Parsec_instInhabited___lam__0___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Internal_Parsec_instInhabited___closed__0_value: crate::leanh::LeanClosureObject<
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
    m_fun: l_Std_Internal_Parsec_instInhabited___lam__0 as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Std_Internal_Parsec_instInhabited___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Internal_Parsec_instInhabited___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Internal_Parsec_instMonad___closed__0_value: crate::leanh::LeanClosureObject<0> =
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
        m_fun: l_Std_Internal_Parsec_instMonad___lam__0 as *const core::ffi::c_void,
        m_arity: 5,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Std_Internal_Parsec_instMonad___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Internal_Parsec_instMonad___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Internal_Parsec_instMonad___closed__1_value: crate::leanh::LeanClosureObject<0> =
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
        m_fun: l_Std_Internal_Parsec_instMonad___lam__1 as *const core::ffi::c_void,
        m_arity: 5,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Std_Internal_Parsec_instMonad___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Internal_Parsec_instMonad___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Internal_Parsec_instMonad___closed__2_value: crate::leanh::LeanClosureObject<0> =
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
        m_fun: l_Std_Internal_Parsec_instMonad___lam__2 as *const core::ffi::c_void,
        m_arity: 3,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Std_Internal_Parsec_instMonad___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Internal_Parsec_instMonad___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Internal_Parsec_instMonad___closed__3_value: crate::leanh::LeanClosureObject<0> =
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
        m_fun: l_Std_Internal_Parsec_instMonad___lam__3 as *const core::ffi::c_void,
        m_arity: 5,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Std_Internal_Parsec_instMonad___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Internal_Parsec_instMonad___closed__3_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Internal_Parsec_instMonad___closed__4_value: crate::leanh::LeanClosureObject<0> =
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
        m_fun: l_Std_Internal_Parsec_instMonad___lam__4 as *const core::ffi::c_void,
        m_arity: 5,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Std_Internal_Parsec_instMonad___closed__4: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Internal_Parsec_instMonad___closed__4_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Internal_Parsec_instMonad___closed__5_value: crate::leanh::LeanClosureObject<0> =
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
        m_fun: l_Std_Internal_Parsec_instMonad___lam__5 as *const core::ffi::c_void,
        m_arity: 5,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Std_Internal_Parsec_instMonad___closed__5: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Internal_Parsec_instMonad___closed__5_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Internal_Parsec_instMonad___closed__6_value: crate::leanh::LeanCtorObject<2> =
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
            core::ptr::addr_of!(l_Std_Internal_Parsec_instMonad___closed__0_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Std_Internal_Parsec_instMonad___closed__1_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Std_Internal_Parsec_instMonad___closed__6: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Internal_Parsec_instMonad___closed__6_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Internal_Parsec_instMonad___closed__7_value: crate::leanh::LeanCtorObject<5> =
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
            core::ptr::addr_of!(l_Std_Internal_Parsec_instMonad___closed__6_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Std_Internal_Parsec_instMonad___closed__2_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Std_Internal_Parsec_instMonad___closed__3_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Std_Internal_Parsec_instMonad___closed__4_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Std_Internal_Parsec_instMonad___closed__5_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Std_Internal_Parsec_instMonad___closed__7: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Internal_Parsec_instMonad___closed__7_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Internal_Parsec_instMonad___closed__8_value: crate::leanh::LeanClosureObject<1> =
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
        m_fun: l_Std_Internal_Parsec_bind as *const core::ffi::c_void,
        m_arity: 6,
        m_num_fixed: 1,
        m_objs: [(((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject],
    };
static mut l_Std_Internal_Parsec_instMonad___closed__8: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Internal_Parsec_instMonad___closed__8_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Internal_Parsec_instMonad___closed__9_value: crate::leanh::LeanCtorObject<2> =
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
            core::ptr::addr_of!(l_Std_Internal_Parsec_instMonad___closed__7_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Std_Internal_Parsec_instMonad___closed__8_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Std_Internal_Parsec_instMonad___closed__9: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Internal_Parsec_instMonad___closed__9_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Internal_Parsec_instAlternative___redArg___closed__0_value:
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
    m_fun: l_Std_Internal_Parsec_instAlternative___redArg___lam__0 as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Std_Internal_Parsec_instAlternative___redArg___closed__0:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Internal_Parsec_instAlternative___redArg___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Internal_Parsec_eof___redArg___closed__0_value: crate::leanh::LeanStringObject<
    22,
> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
static mut l_Std_Internal_Parsec_eof___redArg___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Internal_Parsec_eof___redArg___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Internal_Parsec_eof___redArg___closed__1_value: crate::leanh::LeanCtorObject<1> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Std_Internal_Parsec_eof___redArg___closed__0_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Std_Internal_Parsec_eof___redArg___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Internal_Parsec_eof___redArg___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Internal_Parsec_many___redArg___closed__0_value: crate::leanh::LeanArrayObject<0> =
    crate::leanh::LeanArrayObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<usize>() * 2
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 0)
                as u16,
            other: 0,
            tag: 246,
        },
        m_size: 0,
        m_capacity: 0,
        m_data: [],
    };
static mut l_Std_Internal_Parsec_many___redArg___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Internal_Parsec_many___redArg___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Internal_Parsec_satisfy___redArg___closed__0_value:
    crate::leanh::LeanStringObject<24> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 24,
    m_capacity: 24,
    m_length: 23,
    m_data: [
        99, 111, 110, 100, 105, 116, 105, 111, 110, 32, 110, 111, 116, 32, 115, 97, 116, 105, 115,
        102, 105, 101, 100, 0,
    ],
};
static mut l_Std_Internal_Parsec_satisfy___redArg___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Internal_Parsec_satisfy___redArg___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Internal_Parsec_satisfy___redArg___closed__1_value: crate::leanh::LeanCtorObject<
    1,
> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Std_Internal_Parsec_satisfy___redArg___closed__0_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Std_Internal_Parsec_satisfy___redArg___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Internal_Parsec_satisfy___redArg___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub unsafe fn l_Std_Internal_Parsec_Error_ctorIdx(
    mut v_x_1299_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_1299_) == 0 {
        let mut v___x_1300_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_1300_ = crate::leanh::lean_unsigned_to_nat(0);
        return v___x_1300_;
    } else {
        let mut v___x_1301_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_1301_ = crate::leanh::lean_unsigned_to_nat(1);
        return v___x_1301_;
    }
}
pub unsafe fn l_Std_Internal_Parsec_Error_ctorIdx___boxed(
    mut v_x_1302_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1303_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1303_ = l_Std_Internal_Parsec_Error_ctorIdx(v_x_1302_);
    crate::leanh::lean_dec(v_x_1302_);
    return v_res_1303_;
}
pub unsafe fn l_Std_Internal_Parsec_Error_ctorElim___redArg(
    mut v_t_1304_: *mut crate::leanh::LeanObject,
    mut v_k_1305_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_t_1304_) == 0 {
        return v_k_1305_;
    } else {
        let mut v_s_1306_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1307_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_s_1306_ = crate::leanh::lean_ctor_get(v_t_1304_, 0);
        crate::leanh::lean_inc_ref(v_s_1306_);
        crate::leanh::lean_dec_ref_known(v_t_1304_, 1);
        v___x_1307_ = crate::leanh::lean_apply_1(v_k_1305_, v_s_1306_);
        return v___x_1307_;
    }
}
pub unsafe fn l_Std_Internal_Parsec_Error_ctorElim(
    mut v_motive_1308_: *mut crate::leanh::LeanObject,
    mut v_ctorIdx_1309_: *mut crate::leanh::LeanObject,
    mut v_t_1310_: *mut crate::leanh::LeanObject,
    mut v_h_1311_: *mut crate::leanh::LeanObject,
    mut v_k_1312_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1313_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1313_ = l_Std_Internal_Parsec_Error_ctorElim___redArg(v_t_1310_, v_k_1312_);
    return v___x_1313_;
}
pub unsafe fn l_Std_Internal_Parsec_Error_ctorElim___boxed(
    mut v_motive_1314_: *mut crate::leanh::LeanObject,
    mut v_ctorIdx_1315_: *mut crate::leanh::LeanObject,
    mut v_t_1316_: *mut crate::leanh::LeanObject,
    mut v_h_1317_: *mut crate::leanh::LeanObject,
    mut v_k_1318_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1319_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1319_ = l_Std_Internal_Parsec_Error_ctorElim(
        v_motive_1314_,
        v_ctorIdx_1315_,
        v_t_1316_,
        v_h_1317_,
        v_k_1318_,
    );
    crate::leanh::lean_dec(v_ctorIdx_1315_);
    return v_res_1319_;
}
pub unsafe fn l_Std_Internal_Parsec_Error_eof_elim___redArg(
    mut v_t_1320_: *mut crate::leanh::LeanObject,
    mut v_eof_1321_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1322_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1322_ = l_Std_Internal_Parsec_Error_ctorElim___redArg(v_t_1320_, v_eof_1321_);
    return v___x_1322_;
}
pub unsafe fn l_Std_Internal_Parsec_Error_eof_elim(
    mut v_motive_1323_: *mut crate::leanh::LeanObject,
    mut v_t_1324_: *mut crate::leanh::LeanObject,
    mut v_h_1325_: *mut crate::leanh::LeanObject,
    mut v_eof_1326_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1327_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1327_ = l_Std_Internal_Parsec_Error_ctorElim___redArg(v_t_1324_, v_eof_1326_);
    return v___x_1327_;
}
pub unsafe fn l_Std_Internal_Parsec_Error_other_elim___redArg(
    mut v_t_1328_: *mut crate::leanh::LeanObject,
    mut v_other_1329_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1330_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1330_ = l_Std_Internal_Parsec_Error_ctorElim___redArg(v_t_1328_, v_other_1329_);
    return v___x_1330_;
}
pub unsafe fn l_Std_Internal_Parsec_Error_other_elim(
    mut v_motive_1331_: *mut crate::leanh::LeanObject,
    mut v_t_1332_: *mut crate::leanh::LeanObject,
    mut v_h_1333_: *mut crate::leanh::LeanObject,
    mut v_other_1334_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1335_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1335_ = l_Std_Internal_Parsec_Error_ctorElim___redArg(v_t_1332_, v_other_1334_);
    return v___x_1335_;
}
pub unsafe fn _init_l_Std_Internal_Parsec_instReprError_repr___closed__2()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1339_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1340_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1339_ = crate::leanh::lean_unsigned_to_nat(2);
    v___x_1340_ = lean_nat_to_int(v___x_1339_);
    return v___x_1340_;
}
pub unsafe fn _init_l_Std_Internal_Parsec_instReprError_repr___closed__3()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1341_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1342_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1341_ = crate::leanh::lean_unsigned_to_nat(1);
    v___x_1342_ = lean_nat_to_int(v___x_1341_);
    return v___x_1342_;
}
pub unsafe fn l_Std_Internal_Parsec_instReprError_repr(
    mut v_x_1349_: *mut crate::leanh::LeanObject,
    mut v_prec_1350_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___y_1352_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1353_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1354_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1355_: u8 = 0;
    let mut v___x_1356_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1357_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1358_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1359_: u8 = 0;
    let mut v___x_1360_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1361_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_s_1362_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1364_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1365_: u8 = 0;
    let mut v___y_1367_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1368_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1369_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1371_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1372_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1373_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1374_: u8 = 0;
    let mut v___x_1375_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1376_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1377_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1378_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1379_: u8 = 0;
    let mut v___x_1380_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1381_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1382_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_1349_) == 0 {
                    v___x_1358_ = crate::leanh::lean_unsigned_to_nat(1024);
                    v___x_1359_ = lean_nat_dec_le(v___x_1358_, v_prec_1350_);
                    if v___x_1359_ == 0 {
                        v___x_1360_ = crate::leanh::lean_obj_once(
                            core::ptr::addr_of_mut!(
                                l_Std_Internal_Parsec_instReprError_repr___closed__2
                            ),
                            core::ptr::addr_of_mut!(
                                l_Std_Internal_Parsec_instReprError_repr___closed__2_once
                            ),
                            _init_l_Std_Internal_Parsec_instReprError_repr___closed__2,
                        );
                        v___y_1352_ = v___x_1360_;
                        state = 1;
                        continue;
                    } else {
                        v___x_1361_ = crate::leanh::lean_obj_once(
                            core::ptr::addr_of_mut!(
                                l_Std_Internal_Parsec_instReprError_repr___closed__3
                            ),
                            core::ptr::addr_of_mut!(
                                l_Std_Internal_Parsec_instReprError_repr___closed__3_once
                            ),
                            _init_l_Std_Internal_Parsec_instReprError_repr___closed__3,
                        );
                        v___y_1352_ = v___x_1361_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_s_1362_ = crate::leanh::lean_ctor_get(v_x_1349_, 0);
                    v_isSharedCheck_1382_ = (!crate::leanh::lean_is_exclusive(v_x_1349_)) as u8;
                    if v_isSharedCheck_1382_ == 0 {
                        v___x_1364_ = v_x_1349_;
                        v_isShared_1365_ = v_isSharedCheck_1382_;
                        state = 2;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_s_1362_);
                        crate::leanh::lean_dec(v_x_1349_);
                        v___x_1364_ = crate::leanh::lean_box(0);
                        v_isShared_1365_ = v_isSharedCheck_1382_;
                        state = 2;
                        continue;
                    }
                }
            }
            1 => {
                v___x_1353_ = l_Std_Internal_Parsec_instReprError_repr___closed__1;
                crate::leanh::lean_inc(v___y_1352_);
                v___x_1354_ = crate::leanh::lean_alloc_ctor(4, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1354_, 0, v___y_1352_);
                crate::leanh::lean_ctor_set(v___x_1354_, 1, v___x_1353_);
                v___x_1355_ = 0;
                v___x_1356_ = crate::leanh::lean_alloc_ctor(6, 1, (1) as u32);
                crate::leanh::lean_ctor_set(v___x_1356_, 0, v___x_1354_);
                crate::leanh::lean_ctor_set_uint8(
                    v___x_1356_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                    v___x_1355_,
                );
                v___x_1357_ = l_Repr_addAppParen(v___x_1356_, v_prec_1350_);
                return v___x_1357_;
            }
            2 => {
                v___x_1378_ = crate::leanh::lean_unsigned_to_nat(1024);
                v___x_1379_ = lean_nat_dec_le(v___x_1378_, v_prec_1350_);
                if v___x_1379_ == 0 {
                    v___x_1380_ = crate::leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(
                            l_Std_Internal_Parsec_instReprError_repr___closed__2
                        ),
                        core::ptr::addr_of_mut!(
                            l_Std_Internal_Parsec_instReprError_repr___closed__2_once
                        ),
                        _init_l_Std_Internal_Parsec_instReprError_repr___closed__2,
                    );
                    v___y_1367_ = v___x_1380_;
                    state = 3;
                    continue;
                } else {
                    v___x_1381_ = crate::leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(
                            l_Std_Internal_Parsec_instReprError_repr___closed__3
                        ),
                        core::ptr::addr_of_mut!(
                            l_Std_Internal_Parsec_instReprError_repr___closed__3_once
                        ),
                        _init_l_Std_Internal_Parsec_instReprError_repr___closed__3,
                    );
                    v___y_1367_ = v___x_1381_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_1368_ = l_Std_Internal_Parsec_instReprError_repr___closed__6;
                v___x_1369_ = l_String_quote(v_s_1362_);
                if v_isShared_1365_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_1364_, 3);
                    crate::leanh::lean_ctor_set(v___x_1364_, 0, v___x_1369_);
                    v___x_1371_ = v___x_1364_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1377_ = crate::leanh::lean_alloc_ctor(3, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1377_, 0, v___x_1369_);
                    v___x_1371_ = v_reuseFailAlloc_1377_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_1372_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1372_, 0, v___x_1368_);
                crate::leanh::lean_ctor_set(v___x_1372_, 1, v___x_1371_);
                crate::leanh::lean_inc(v___y_1367_);
                v___x_1373_ = crate::leanh::lean_alloc_ctor(4, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1373_, 0, v___y_1367_);
                crate::leanh::lean_ctor_set(v___x_1373_, 1, v___x_1372_);
                v___x_1374_ = 0;
                v___x_1375_ = crate::leanh::lean_alloc_ctor(6, 1, (1) as u32);
                crate::leanh::lean_ctor_set(v___x_1375_, 0, v___x_1373_);
                crate::leanh::lean_ctor_set_uint8(
                    v___x_1375_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                    v___x_1374_,
                );
                v___x_1376_ = l_Repr_addAppParen(v___x_1375_, v_prec_1350_);
                return v___x_1376_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Internal_Parsec_instReprError_repr___boxed(
    mut v_x_1383_: *mut crate::leanh::LeanObject,
    mut v_prec_1384_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1385_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1385_ = l_Std_Internal_Parsec_instReprError_repr(v_x_1383_, v_prec_1384_);
    crate::leanh::lean_dec(v_prec_1384_);
    return v_res_1385_;
}
pub unsafe fn l_Std_Internal_Parsec_instToStringError___lam__0(
    mut v_x_1389_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_1389_) == 0 {
        let mut v___x_1390_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_1390_ = l_Std_Internal_Parsec_instToStringError___lam__0___closed__0;
        return v___x_1390_;
    } else {
        let mut v_s_1391_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_s_1391_ = crate::leanh::lean_ctor_get(v_x_1389_, 0);
        crate::leanh::lean_inc_ref(v_s_1391_);
        return v_s_1391_;
    }
}
pub unsafe fn l_Std_Internal_Parsec_instToStringError___lam__0___boxed(
    mut v_x_1392_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1393_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1393_ = l_Std_Internal_Parsec_instToStringError___lam__0(v_x_1392_);
    crate::leanh::lean_dec(v_x_1392_);
    return v_res_1393_;
}
pub unsafe fn l_Std_Internal_Parsec_ParseResult_ctorIdx___redArg(
    mut v_x_1396_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_1396_) == 0 {
        let mut v___x_1397_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_1397_ = crate::leanh::lean_unsigned_to_nat(0);
        return v___x_1397_;
    } else {
        let mut v___x_1398_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_1398_ = crate::leanh::lean_unsigned_to_nat(1);
        return v___x_1398_;
    }
}
pub unsafe fn l_Std_Internal_Parsec_ParseResult_ctorIdx___redArg___boxed(
    mut v_x_1399_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1400_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1400_ = l_Std_Internal_Parsec_ParseResult_ctorIdx___redArg(v_x_1399_);
    crate::leanh::lean_dec_ref(v_x_1399_);
    return v_res_1400_;
}
pub unsafe fn l_Std_Internal_Parsec_ParseResult_ctorIdx(
    mut v_00_u03b1_1401_: *mut crate::leanh::LeanObject,
    mut v_00_u03b9_1402_: *mut crate::leanh::LeanObject,
    mut v_x_1403_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1404_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1404_ = l_Std_Internal_Parsec_ParseResult_ctorIdx___redArg(v_x_1403_);
    return v___x_1404_;
}
pub unsafe fn l_Std_Internal_Parsec_ParseResult_ctorIdx___boxed(
    mut v_00_u03b1_1405_: *mut crate::leanh::LeanObject,
    mut v_00_u03b9_1406_: *mut crate::leanh::LeanObject,
    mut v_x_1407_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1408_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1408_ =
        l_Std_Internal_Parsec_ParseResult_ctorIdx(v_00_u03b1_1405_, v_00_u03b9_1406_, v_x_1407_);
    crate::leanh::lean_dec_ref(v_x_1407_);
    return v_res_1408_;
}
pub unsafe fn l_Std_Internal_Parsec_ParseResult_ctorElim___redArg(
    mut v_t_1409_: *mut crate::leanh::LeanObject,
    mut v_k_1410_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_pos_1411_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_res_1412_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1413_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_pos_1411_ = crate::leanh::lean_ctor_get(v_t_1409_, 0);
    crate::leanh::lean_inc(v_pos_1411_);
    v_res_1412_ = crate::leanh::lean_ctor_get(v_t_1409_, 1);
    crate::leanh::lean_inc(v_res_1412_);
    crate::leanh::lean_dec_ref(v_t_1409_);
    v___x_1413_ = crate::leanh::lean_apply_2(v_k_1410_, v_pos_1411_, v_res_1412_);
    return v___x_1413_;
}
pub unsafe fn l_Std_Internal_Parsec_ParseResult_ctorElim(
    mut v_00_u03b1_1414_: *mut crate::leanh::LeanObject,
    mut v_00_u03b9_1415_: *mut crate::leanh::LeanObject,
    mut v_motive_1416_: *mut crate::leanh::LeanObject,
    mut v_ctorIdx_1417_: *mut crate::leanh::LeanObject,
    mut v_t_1418_: *mut crate::leanh::LeanObject,
    mut v_h_1419_: *mut crate::leanh::LeanObject,
    mut v_k_1420_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1421_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1421_ = l_Std_Internal_Parsec_ParseResult_ctorElim___redArg(v_t_1418_, v_k_1420_);
    return v___x_1421_;
}
pub unsafe fn l_Std_Internal_Parsec_ParseResult_ctorElim___boxed(
    mut v_00_u03b1_1422_: *mut crate::leanh::LeanObject,
    mut v_00_u03b9_1423_: *mut crate::leanh::LeanObject,
    mut v_motive_1424_: *mut crate::leanh::LeanObject,
    mut v_ctorIdx_1425_: *mut crate::leanh::LeanObject,
    mut v_t_1426_: *mut crate::leanh::LeanObject,
    mut v_h_1427_: *mut crate::leanh::LeanObject,
    mut v_k_1428_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1429_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1429_ = l_Std_Internal_Parsec_ParseResult_ctorElim(
        v_00_u03b1_1422_,
        v_00_u03b9_1423_,
        v_motive_1424_,
        v_ctorIdx_1425_,
        v_t_1426_,
        v_h_1427_,
        v_k_1428_,
    );
    crate::leanh::lean_dec(v_ctorIdx_1425_);
    return v_res_1429_;
}
pub unsafe fn l_Std_Internal_Parsec_ParseResult_success_elim___redArg(
    mut v_t_1430_: *mut crate::leanh::LeanObject,
    mut v_success_1431_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1432_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1432_ = l_Std_Internal_Parsec_ParseResult_ctorElim___redArg(v_t_1430_, v_success_1431_);
    return v___x_1432_;
}
pub unsafe fn l_Std_Internal_Parsec_ParseResult_success_elim(
    mut v_00_u03b1_1433_: *mut crate::leanh::LeanObject,
    mut v_00_u03b9_1434_: *mut crate::leanh::LeanObject,
    mut v_motive_1435_: *mut crate::leanh::LeanObject,
    mut v_t_1436_: *mut crate::leanh::LeanObject,
    mut v_h_1437_: *mut crate::leanh::LeanObject,
    mut v_success_1438_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1439_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1439_ = l_Std_Internal_Parsec_ParseResult_ctorElim___redArg(v_t_1436_, v_success_1438_);
    return v___x_1439_;
}
pub unsafe fn l_Std_Internal_Parsec_ParseResult_error_elim___redArg(
    mut v_t_1440_: *mut crate::leanh::LeanObject,
    mut v_error_1441_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1442_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1442_ = l_Std_Internal_Parsec_ParseResult_ctorElim___redArg(v_t_1440_, v_error_1441_);
    return v___x_1442_;
}
pub unsafe fn l_Std_Internal_Parsec_ParseResult_error_elim(
    mut v_00_u03b1_1443_: *mut crate::leanh::LeanObject,
    mut v_00_u03b9_1444_: *mut crate::leanh::LeanObject,
    mut v_motive_1445_: *mut crate::leanh::LeanObject,
    mut v_t_1446_: *mut crate::leanh::LeanObject,
    mut v_h_1447_: *mut crate::leanh::LeanObject,
    mut v_error_1448_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1449_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1449_ = l_Std_Internal_Parsec_ParseResult_ctorElim___redArg(v_t_1446_, v_error_1448_);
    return v___x_1449_;
}
pub unsafe fn l_Std_Internal_Parsec_instReprParseResult_repr___redArg(
    mut v_inst_1462_: *mut crate::leanh::LeanObject,
    mut v_inst_1463_: *mut crate::leanh::LeanObject,
    mut v_x_1464_: *mut crate::leanh::LeanObject,
    mut v_prec_1465_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_pos_1466_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_res_1467_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1469_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1470_: u8 = 0;
    let mut v___y_1472_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1473_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1474_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1475_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1476_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1478_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1479_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1480_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1481_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1482_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1483_: u8 = 0;
    let mut v___x_1484_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1485_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1486_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1487_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1488_: u8 = 0;
    let mut v___x_1489_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1490_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1491_: u8 = 0;
    let mut v_pos_1492_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_err_1493_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1495_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1496_: u8 = 0;
    let mut v___y_1498_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1499_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1500_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1501_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1502_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1504_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1505_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1506_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1507_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1508_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1509_: u8 = 0;
    let mut v___x_1510_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1511_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1512_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1513_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1514_: u8 = 0;
    let mut v___x_1515_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1516_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1517_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_1464_) == 0 {
                    v_pos_1466_ = crate::leanh::lean_ctor_get(v_x_1464_, 0);
                    v_res_1467_ = crate::leanh::lean_ctor_get(v_x_1464_, 1);
                    v_isSharedCheck_1491_ = (!crate::leanh::lean_is_exclusive(v_x_1464_)) as u8;
                    if v_isSharedCheck_1491_ == 0 {
                        v___x_1469_ = v_x_1464_;
                        v_isShared_1470_ = v_isSharedCheck_1491_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_res_1467_);
                        crate::leanh::lean_inc(v_pos_1466_);
                        crate::leanh::lean_dec(v_x_1464_);
                        v___x_1469_ = crate::leanh::lean_box(0);
                        v_isShared_1470_ = v_isSharedCheck_1491_;
                        state = 1;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_inst_1462_);
                    v_pos_1492_ = crate::leanh::lean_ctor_get(v_x_1464_, 0);
                    v_err_1493_ = crate::leanh::lean_ctor_get(v_x_1464_, 1);
                    v_isSharedCheck_1517_ = (!crate::leanh::lean_is_exclusive(v_x_1464_)) as u8;
                    if v_isSharedCheck_1517_ == 0 {
                        v___x_1495_ = v_x_1464_;
                        v_isShared_1496_ = v_isSharedCheck_1517_;
                        state = 4;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_err_1493_);
                        crate::leanh::lean_inc(v_pos_1492_);
                        crate::leanh::lean_dec(v_x_1464_);
                        v___x_1495_ = crate::leanh::lean_box(0);
                        v_isShared_1496_ = v_isSharedCheck_1517_;
                        state = 4;
                        continue;
                    }
                }
            }
            1 => {
                v___x_1487_ = crate::leanh::lean_unsigned_to_nat(1024);
                v___x_1488_ = lean_nat_dec_le(v___x_1487_, v_prec_1465_);
                if v___x_1488_ == 0 {
                    v___x_1489_ = crate::leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(
                            l_Std_Internal_Parsec_instReprError_repr___closed__2
                        ),
                        core::ptr::addr_of_mut!(
                            l_Std_Internal_Parsec_instReprError_repr___closed__2_once
                        ),
                        _init_l_Std_Internal_Parsec_instReprError_repr___closed__2,
                    );
                    v___y_1472_ = v___x_1489_;
                    state = 2;
                    continue;
                } else {
                    v___x_1490_ = crate::leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(
                            l_Std_Internal_Parsec_instReprError_repr___closed__3
                        ),
                        core::ptr::addr_of_mut!(
                            l_Std_Internal_Parsec_instReprError_repr___closed__3_once
                        ),
                        _init_l_Std_Internal_Parsec_instReprError_repr___closed__3,
                    );
                    v___y_1472_ = v___x_1490_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_1473_ = crate::leanh::lean_box(1);
                v___x_1474_ = l_Std_Internal_Parsec_instReprParseResult_repr___redArg___closed__2;
                v___x_1475_ = crate::leanh::lean_unsigned_to_nat(1024);
                v___x_1476_ = crate::leanh::lean_apply_2(v_inst_1463_, v_pos_1466_, v___x_1475_);
                if v_isShared_1470_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_1469_, 5);
                    crate::leanh::lean_ctor_set(v___x_1469_, 1, v___x_1476_);
                    crate::leanh::lean_ctor_set(v___x_1469_, 0, v___x_1474_);
                    v___x_1478_ = v___x_1469_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_1486_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1486_, 0, v___x_1474_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1486_, 1, v___x_1476_);
                    v___x_1478_ = v_reuseFailAlloc_1486_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_1479_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1479_, 0, v___x_1478_);
                crate::leanh::lean_ctor_set(v___x_1479_, 1, v___x_1473_);
                v___x_1480_ = crate::leanh::lean_apply_2(v_inst_1462_, v_res_1467_, v___x_1475_);
                v___x_1481_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1481_, 0, v___x_1479_);
                crate::leanh::lean_ctor_set(v___x_1481_, 1, v___x_1480_);
                crate::leanh::lean_inc(v___y_1472_);
                v___x_1482_ = crate::leanh::lean_alloc_ctor(4, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1482_, 0, v___y_1472_);
                crate::leanh::lean_ctor_set(v___x_1482_, 1, v___x_1481_);
                v___x_1483_ = 0;
                v___x_1484_ = crate::leanh::lean_alloc_ctor(6, 1, (1) as u32);
                crate::leanh::lean_ctor_set(v___x_1484_, 0, v___x_1482_);
                crate::leanh::lean_ctor_set_uint8(
                    v___x_1484_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                    v___x_1483_,
                );
                v___x_1485_ = l_Repr_addAppParen(v___x_1484_, v_prec_1465_);
                return v___x_1485_;
            }
            4 => {
                v___x_1513_ = crate::leanh::lean_unsigned_to_nat(1024);
                v___x_1514_ = lean_nat_dec_le(v___x_1513_, v_prec_1465_);
                if v___x_1514_ == 0 {
                    v___x_1515_ = crate::leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(
                            l_Std_Internal_Parsec_instReprError_repr___closed__2
                        ),
                        core::ptr::addr_of_mut!(
                            l_Std_Internal_Parsec_instReprError_repr___closed__2_once
                        ),
                        _init_l_Std_Internal_Parsec_instReprError_repr___closed__2,
                    );
                    v___y_1498_ = v___x_1515_;
                    state = 5;
                    continue;
                } else {
                    v___x_1516_ = crate::leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(
                            l_Std_Internal_Parsec_instReprError_repr___closed__3
                        ),
                        core::ptr::addr_of_mut!(
                            l_Std_Internal_Parsec_instReprError_repr___closed__3_once
                        ),
                        _init_l_Std_Internal_Parsec_instReprError_repr___closed__3,
                    );
                    v___y_1498_ = v___x_1516_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                v___x_1499_ = crate::leanh::lean_box(1);
                v___x_1500_ = l_Std_Internal_Parsec_instReprParseResult_repr___redArg___closed__5;
                v___x_1501_ = crate::leanh::lean_unsigned_to_nat(1024);
                v___x_1502_ = crate::leanh::lean_apply_2(v_inst_1463_, v_pos_1492_, v___x_1501_);
                if v_isShared_1496_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_1495_, 5);
                    crate::leanh::lean_ctor_set(v___x_1495_, 1, v___x_1502_);
                    crate::leanh::lean_ctor_set(v___x_1495_, 0, v___x_1500_);
                    v___x_1504_ = v___x_1495_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_1512_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1512_, 0, v___x_1500_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1512_, 1, v___x_1502_);
                    v___x_1504_ = v_reuseFailAlloc_1512_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                v___x_1505_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1505_, 0, v___x_1504_);
                crate::leanh::lean_ctor_set(v___x_1505_, 1, v___x_1499_);
                v___x_1506_ = l_Std_Internal_Parsec_instReprError_repr(v_err_1493_, v___x_1501_);
                v___x_1507_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1507_, 0, v___x_1505_);
                crate::leanh::lean_ctor_set(v___x_1507_, 1, v___x_1506_);
                crate::leanh::lean_inc(v___y_1498_);
                v___x_1508_ = crate::leanh::lean_alloc_ctor(4, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1508_, 0, v___y_1498_);
                crate::leanh::lean_ctor_set(v___x_1508_, 1, v___x_1507_);
                v___x_1509_ = 0;
                v___x_1510_ = crate::leanh::lean_alloc_ctor(6, 1, (1) as u32);
                crate::leanh::lean_ctor_set(v___x_1510_, 0, v___x_1508_);
                crate::leanh::lean_ctor_set_uint8(
                    v___x_1510_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                    v___x_1509_,
                );
                v___x_1511_ = l_Repr_addAppParen(v___x_1510_, v_prec_1465_);
                return v___x_1511_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Internal_Parsec_instReprParseResult_repr___redArg___boxed(
    mut v_inst_1518_: *mut crate::leanh::LeanObject,
    mut v_inst_1519_: *mut crate::leanh::LeanObject,
    mut v_x_1520_: *mut crate::leanh::LeanObject,
    mut v_prec_1521_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1522_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1522_ = l_Std_Internal_Parsec_instReprParseResult_repr___redArg(
        v_inst_1518_,
        v_inst_1519_,
        v_x_1520_,
        v_prec_1521_,
    );
    crate::leanh::lean_dec(v_prec_1521_);
    return v_res_1522_;
}
pub unsafe fn l_Std_Internal_Parsec_instReprParseResult_repr(
    mut v_00_u03b1_1523_: *mut crate::leanh::LeanObject,
    mut v_00_u03b9_1524_: *mut crate::leanh::LeanObject,
    mut v_inst_1525_: *mut crate::leanh::LeanObject,
    mut v_inst_1526_: *mut crate::leanh::LeanObject,
    mut v_x_1527_: *mut crate::leanh::LeanObject,
    mut v_prec_1528_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1529_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1529_ = l_Std_Internal_Parsec_instReprParseResult_repr___redArg(
        v_inst_1525_,
        v_inst_1526_,
        v_x_1527_,
        v_prec_1528_,
    );
    return v___x_1529_;
}
pub unsafe fn l_Std_Internal_Parsec_instReprParseResult_repr___boxed(
    mut v_00_u03b1_1530_: *mut crate::leanh::LeanObject,
    mut v_00_u03b9_1531_: *mut crate::leanh::LeanObject,
    mut v_inst_1532_: *mut crate::leanh::LeanObject,
    mut v_inst_1533_: *mut crate::leanh::LeanObject,
    mut v_x_1534_: *mut crate::leanh::LeanObject,
    mut v_prec_1535_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1536_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1536_ = l_Std_Internal_Parsec_instReprParseResult_repr(
        v_00_u03b1_1530_,
        v_00_u03b9_1531_,
        v_inst_1532_,
        v_inst_1533_,
        v_x_1534_,
        v_prec_1535_,
    );
    crate::leanh::lean_dec(v_prec_1535_);
    return v_res_1536_;
}
pub unsafe fn l_Std_Internal_Parsec_instReprParseResult___redArg(
    mut v_inst_1537_: *mut crate::leanh::LeanObject,
    mut v_inst_1538_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1539_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1539_ = crate::leanh::lean_alloc_closure(
        l_Std_Internal_Parsec_instReprParseResult_repr___boxed as *mut core::ffi::c_void,
        6,
        4,
    );
    crate::leanh::lean_closure_set(v___x_1539_, 0, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_1539_, 1, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_1539_, 2, v_inst_1537_);
    crate::leanh::lean_closure_set(v___x_1539_, 3, v_inst_1538_);
    return v___x_1539_;
}
pub unsafe fn l_Std_Internal_Parsec_instReprParseResult(
    mut v_00_u03b1_1540_: *mut crate::leanh::LeanObject,
    mut v_00_u03b9_1541_: *mut crate::leanh::LeanObject,
    mut v_inst_1542_: *mut crate::leanh::LeanObject,
    mut v_inst_1543_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1544_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1544_ = crate::leanh::lean_alloc_closure(
        l_Std_Internal_Parsec_instReprParseResult_repr___boxed as *mut core::ffi::c_void,
        6,
        4,
    );
    crate::leanh::lean_closure_set(v___x_1544_, 0, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_1544_, 1, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_1544_, 2, v_inst_1542_);
    crate::leanh::lean_closure_set(v___x_1544_, 3, v_inst_1543_);
    return v___x_1544_;
}
pub unsafe fn l_Std_Internal_Parsec_instInhabited___lam__0(
    mut v_it_1548_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1549_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1550_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1549_ = l_Std_Internal_Parsec_instInhabited___lam__0___closed__1;
    v___x_1550_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1550_, 0, v_it_1548_);
    crate::leanh::lean_ctor_set(v___x_1550_, 1, v___x_1549_);
    return v___x_1550_;
}
pub unsafe fn l_Std_Internal_Parsec_instInhabited(
    mut v_00_u03b1_1552_: *mut crate::leanh::LeanObject,
    mut v_00_u03b9_1553_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_1554_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_1554_ = l_Std_Internal_Parsec_instInhabited___closed__0;
    return v___f_1554_;
}
pub unsafe fn l_Std_Internal_Parsec_pure___redArg(
    mut v_a_1555_: *mut crate::leanh::LeanObject,
    mut v_it_1556_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1557_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1557_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1557_, 0, v_it_1556_);
    crate::leanh::lean_ctor_set(v___x_1557_, 1, v_a_1555_);
    return v___x_1557_;
}
pub unsafe fn l_Std_Internal_Parsec_pure(
    mut v_00_u03b1_1558_: *mut crate::leanh::LeanObject,
    mut v_00_u03b9_1559_: *mut crate::leanh::LeanObject,
    mut v_a_1560_: *mut crate::leanh::LeanObject,
    mut v_it_1561_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1562_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1562_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1562_, 0, v_it_1561_);
    crate::leanh::lean_ctor_set(v___x_1562_, 1, v_a_1560_);
    return v___x_1562_;
}
pub unsafe fn l_Std_Internal_Parsec_bind___redArg(
    mut v_f_1563_: *mut crate::leanh::LeanObject,
    mut v_g_1564_: *mut crate::leanh::LeanObject,
    mut v_it_1565_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1566_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_pos_1567_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_res_1568_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1569_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_pos_1570_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_err_1571_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1573_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1574_: u8 = 0;
    let mut v___x_1576_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1577_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1578_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1566_ = crate::leanh::lean_apply_1(v_f_1563_, v_it_1565_);
                if crate::leanh::lean_obj_tag(v___x_1566_) == 0 {
                    v_pos_1567_ = crate::leanh::lean_ctor_get(v___x_1566_, 0);
                    crate::leanh::lean_inc(v_pos_1567_);
                    v_res_1568_ = crate::leanh::lean_ctor_get(v___x_1566_, 1);
                    crate::leanh::lean_inc(v_res_1568_);
                    crate::leanh::lean_dec_ref_known(v___x_1566_, 2);
                    v___x_1569_ = crate::leanh::lean_apply_2(v_g_1564_, v_res_1568_, v_pos_1567_);
                    return v___x_1569_;
                } else {
                    crate::leanh::lean_dec_ref(v_g_1564_);
                    v_pos_1570_ = crate::leanh::lean_ctor_get(v___x_1566_, 0);
                    v_err_1571_ = crate::leanh::lean_ctor_get(v___x_1566_, 1);
                    v_isSharedCheck_1578_ = (!crate::leanh::lean_is_exclusive(v___x_1566_)) as u8;
                    if v_isSharedCheck_1578_ == 0 {
                        v___x_1573_ = v___x_1566_;
                        v_isShared_1574_ = v_isSharedCheck_1578_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_err_1571_);
                        crate::leanh::lean_inc(v_pos_1570_);
                        crate::leanh::lean_dec(v___x_1566_);
                        v___x_1573_ = crate::leanh::lean_box(0);
                        v_isShared_1574_ = v_isSharedCheck_1578_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_1574_ == 0 {
                    v___x_1576_ = v___x_1573_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1577_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1577_, 0, v_pos_1570_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1577_, 1, v_err_1571_);
                    v___x_1576_ = v_reuseFailAlloc_1577_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1576_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Internal_Parsec_bind(
    mut v_00_u03b9_1579_: *mut crate::leanh::LeanObject,
    mut v_00_u03b1_1580_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_1581_: *mut crate::leanh::LeanObject,
    mut v_f_1582_: *mut crate::leanh::LeanObject,
    mut v_g_1583_: *mut crate::leanh::LeanObject,
    mut v_it_1584_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1585_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_pos_1586_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_res_1587_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1588_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_pos_1589_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_err_1590_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1592_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1593_: u8 = 0;
    let mut v___x_1595_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1596_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1597_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1585_ = crate::leanh::lean_apply_1(v_f_1582_, v_it_1584_);
                if crate::leanh::lean_obj_tag(v___x_1585_) == 0 {
                    v_pos_1586_ = crate::leanh::lean_ctor_get(v___x_1585_, 0);
                    crate::leanh::lean_inc(v_pos_1586_);
                    v_res_1587_ = crate::leanh::lean_ctor_get(v___x_1585_, 1);
                    crate::leanh::lean_inc(v_res_1587_);
                    crate::leanh::lean_dec_ref_known(v___x_1585_, 2);
                    v___x_1588_ = crate::leanh::lean_apply_2(v_g_1583_, v_res_1587_, v_pos_1586_);
                    return v___x_1588_;
                } else {
                    crate::leanh::lean_dec_ref(v_g_1583_);
                    v_pos_1589_ = crate::leanh::lean_ctor_get(v___x_1585_, 0);
                    v_err_1590_ = crate::leanh::lean_ctor_get(v___x_1585_, 1);
                    v_isSharedCheck_1597_ = (!crate::leanh::lean_is_exclusive(v___x_1585_)) as u8;
                    if v_isSharedCheck_1597_ == 0 {
                        v___x_1592_ = v___x_1585_;
                        v_isShared_1593_ = v_isSharedCheck_1597_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_err_1590_);
                        crate::leanh::lean_inc(v_pos_1589_);
                        crate::leanh::lean_dec(v___x_1585_);
                        v___x_1592_ = crate::leanh::lean_box(0);
                        v_isShared_1593_ = v_isSharedCheck_1597_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_1593_ == 0 {
                    v___x_1595_ = v___x_1592_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1596_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1596_, 0, v_pos_1589_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1596_, 1, v_err_1590_);
                    v___x_1595_ = v_reuseFailAlloc_1596_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1595_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Internal_Parsec_fail___redArg(
    mut v_msg_1598_: *mut crate::leanh::LeanObject,
    mut v_it_1599_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1600_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1601_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1600_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1600_, 0, v_msg_1598_);
    v___x_1601_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1601_, 0, v_it_1599_);
    crate::leanh::lean_ctor_set(v___x_1601_, 1, v___x_1600_);
    return v___x_1601_;
}
pub unsafe fn l_Std_Internal_Parsec_fail(
    mut v_00_u03b1_1602_: *mut crate::leanh::LeanObject,
    mut v_00_u03b9_1603_: *mut crate::leanh::LeanObject,
    mut v_msg_1604_: *mut crate::leanh::LeanObject,
    mut v_it_1605_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1606_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1607_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1606_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1606_, 0, v_msg_1604_);
    v___x_1607_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1607_, 0, v_it_1605_);
    crate::leanh::lean_ctor_set(v___x_1607_, 1, v___x_1606_);
    return v___x_1607_;
}
pub unsafe fn l_Std_Internal_Parsec_tryCatch___redArg(
    mut v_inst_1608_: *mut crate::leanh::LeanObject,
    mut v_inst_1609_: *mut crate::leanh::LeanObject,
    mut v_p_1610_: *mut crate::leanh::LeanObject,
    mut v_csuccess_1611_: *mut crate::leanh::LeanObject,
    mut v_cerror_1612_: *mut crate::leanh::LeanObject,
    mut v_it_1613_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1614_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_pos_1615_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_res_1616_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1617_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_pos_1618_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_err_1619_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1621_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1622_: u8 = 0;
    let mut v_pos_1623_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1624_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1625_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1626_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1627_: u8 = 0;
    let mut v___x_1629_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1630_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1631_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1632_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1633_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                crate::leanh::lean_inc(v_it_1613_);
                v___x_1614_ = crate::leanh::lean_apply_1(v_p_1610_, v_it_1613_);
                if crate::leanh::lean_obj_tag(v___x_1614_) == 0 {
                    crate::leanh::lean_dec(v_it_1613_);
                    crate::leanh::lean_dec_ref(v_cerror_1612_);
                    crate::leanh::lean_dec_ref(v_inst_1609_);
                    crate::leanh::lean_dec_ref(v_inst_1608_);
                    v_pos_1615_ = crate::leanh::lean_ctor_get(v___x_1614_, 0);
                    crate::leanh::lean_inc(v_pos_1615_);
                    v_res_1616_ = crate::leanh::lean_ctor_get(v___x_1614_, 1);
                    crate::leanh::lean_inc(v_res_1616_);
                    crate::leanh::lean_dec_ref_known(v___x_1614_, 2);
                    v___x_1617_ =
                        crate::leanh::lean_apply_2(v_csuccess_1611_, v_res_1616_, v_pos_1615_);
                    return v___x_1617_;
                } else {
                    crate::leanh::lean_dec_ref(v_csuccess_1611_);
                    v_pos_1618_ = crate::leanh::lean_ctor_get(v___x_1614_, 0);
                    v_err_1619_ = crate::leanh::lean_ctor_get(v___x_1614_, 1);
                    v_isSharedCheck_1633_ = (!crate::leanh::lean_is_exclusive(v___x_1614_)) as u8;
                    if v_isSharedCheck_1633_ == 0 {
                        v___x_1621_ = v___x_1614_;
                        v_isShared_1622_ = v_isSharedCheck_1633_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_err_1619_);
                        crate::leanh::lean_inc(v_pos_1618_);
                        crate::leanh::lean_dec(v___x_1614_);
                        v___x_1621_ = crate::leanh::lean_box(0);
                        v_isShared_1622_ = v_isSharedCheck_1633_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v_pos_1623_ = crate::leanh::lean_ctor_get(v_inst_1609_, 0);
                crate::leanh::lean_inc_n(v_pos_1623_, 2);
                crate::leanh::lean_dec_ref(v_inst_1609_);
                v___x_1624_ = crate::leanh::lean_apply_1(v_pos_1623_, v_it_1613_);
                crate::leanh::lean_inc(v_pos_1618_);
                v___x_1625_ = crate::leanh::lean_apply_1(v_pos_1623_, v_pos_1618_);
                v___x_1626_ = crate::leanh::lean_apply_2(v_inst_1608_, v___x_1624_, v___x_1625_);
                v___x_1627_ = (crate::leanh::lean_unbox(v___x_1626_) as u8);
                if v___x_1627_ == 0 {
                    crate::leanh::lean_dec_ref(v_cerror_1612_);
                    if v_isShared_1622_ == 0 {
                        v___x_1629_ = v___x_1621_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_1630_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1630_, 0, v_pos_1618_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1630_, 1, v_err_1619_);
                        v___x_1629_ = v_reuseFailAlloc_1630_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_1621_);
                    crate::leanh::lean_dec(v_err_1619_);
                    v___x_1631_ = crate::leanh::lean_box(0);
                    v___x_1632_ =
                        crate::leanh::lean_apply_2(v_cerror_1612_, v___x_1631_, v_pos_1618_);
                    return v___x_1632_;
                }
            }
            2 => {
                return v___x_1629_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Internal_Parsec_tryCatch(
    mut v_00_u03b1_1634_: *mut crate::leanh::LeanObject,
    mut v_00_u03b9_1635_: *mut crate::leanh::LeanObject,
    mut v_elem_1636_: *mut crate::leanh::LeanObject,
    mut v_idx_1637_: *mut crate::leanh::LeanObject,
    mut v_inst_1638_: *mut crate::leanh::LeanObject,
    mut v_inst_1639_: *mut crate::leanh::LeanObject,
    mut v_inst_1640_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_1641_: *mut crate::leanh::LeanObject,
    mut v_p_1642_: *mut crate::leanh::LeanObject,
    mut v_csuccess_1643_: *mut crate::leanh::LeanObject,
    mut v_cerror_1644_: *mut crate::leanh::LeanObject,
    mut v_it_1645_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1646_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_pos_1647_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_res_1648_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1649_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_pos_1650_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_err_1651_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1653_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1654_: u8 = 0;
    let mut v_pos_1655_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1656_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1657_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1658_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1659_: u8 = 0;
    let mut v___x_1661_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1662_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1663_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1664_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1665_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                crate::leanh::lean_inc(v_it_1645_);
                v___x_1646_ = crate::leanh::lean_apply_1(v_p_1642_, v_it_1645_);
                if crate::leanh::lean_obj_tag(v___x_1646_) == 0 {
                    crate::leanh::lean_dec(v_it_1645_);
                    crate::leanh::lean_dec_ref(v_cerror_1644_);
                    crate::leanh::lean_dec_ref(v_inst_1640_);
                    crate::leanh::lean_dec_ref(v_inst_1638_);
                    v_pos_1647_ = crate::leanh::lean_ctor_get(v___x_1646_, 0);
                    crate::leanh::lean_inc(v_pos_1647_);
                    v_res_1648_ = crate::leanh::lean_ctor_get(v___x_1646_, 1);
                    crate::leanh::lean_inc(v_res_1648_);
                    crate::leanh::lean_dec_ref_known(v___x_1646_, 2);
                    v___x_1649_ =
                        crate::leanh::lean_apply_2(v_csuccess_1643_, v_res_1648_, v_pos_1647_);
                    return v___x_1649_;
                } else {
                    crate::leanh::lean_dec_ref(v_csuccess_1643_);
                    v_pos_1650_ = crate::leanh::lean_ctor_get(v___x_1646_, 0);
                    v_err_1651_ = crate::leanh::lean_ctor_get(v___x_1646_, 1);
                    v_isSharedCheck_1665_ = (!crate::leanh::lean_is_exclusive(v___x_1646_)) as u8;
                    if v_isSharedCheck_1665_ == 0 {
                        v___x_1653_ = v___x_1646_;
                        v_isShared_1654_ = v_isSharedCheck_1665_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_err_1651_);
                        crate::leanh::lean_inc(v_pos_1650_);
                        crate::leanh::lean_dec(v___x_1646_);
                        v___x_1653_ = crate::leanh::lean_box(0);
                        v_isShared_1654_ = v_isSharedCheck_1665_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v_pos_1655_ = crate::leanh::lean_ctor_get(v_inst_1640_, 0);
                crate::leanh::lean_inc_n(v_pos_1655_, 2);
                crate::leanh::lean_dec_ref(v_inst_1640_);
                v___x_1656_ = crate::leanh::lean_apply_1(v_pos_1655_, v_it_1645_);
                crate::leanh::lean_inc(v_pos_1650_);
                v___x_1657_ = crate::leanh::lean_apply_1(v_pos_1655_, v_pos_1650_);
                v___x_1658_ = crate::leanh::lean_apply_2(v_inst_1638_, v___x_1656_, v___x_1657_);
                v___x_1659_ = (crate::leanh::lean_unbox(v___x_1658_) as u8);
                if v___x_1659_ == 0 {
                    crate::leanh::lean_dec_ref(v_cerror_1644_);
                    if v_isShared_1654_ == 0 {
                        v___x_1661_ = v___x_1653_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_1662_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1662_, 0, v_pos_1650_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1662_, 1, v_err_1651_);
                        v___x_1661_ = v_reuseFailAlloc_1662_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_1653_);
                    crate::leanh::lean_dec(v_err_1651_);
                    v___x_1663_ = crate::leanh::lean_box(0);
                    v___x_1664_ =
                        crate::leanh::lean_apply_2(v_cerror_1644_, v___x_1663_, v_pos_1650_);
                    return v___x_1664_;
                }
            }
            2 => {
                return v___x_1661_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Internal_Parsec_tryCatch___boxed(
    mut v_00_u03b1_1666_: *mut crate::leanh::LeanObject,
    mut v_00_u03b9_1667_: *mut crate::leanh::LeanObject,
    mut v_elem_1668_: *mut crate::leanh::LeanObject,
    mut v_idx_1669_: *mut crate::leanh::LeanObject,
    mut v_inst_1670_: *mut crate::leanh::LeanObject,
    mut v_inst_1671_: *mut crate::leanh::LeanObject,
    mut v_inst_1672_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_1673_: *mut crate::leanh::LeanObject,
    mut v_p_1674_: *mut crate::leanh::LeanObject,
    mut v_csuccess_1675_: *mut crate::leanh::LeanObject,
    mut v_cerror_1676_: *mut crate::leanh::LeanObject,
    mut v_it_1677_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1678_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1678_ = l_Std_Internal_Parsec_tryCatch(
        v_00_u03b1_1666_,
        v_00_u03b9_1667_,
        v_elem_1668_,
        v_idx_1669_,
        v_inst_1670_,
        v_inst_1671_,
        v_inst_1672_,
        v_00_u03b2_1673_,
        v_p_1674_,
        v_csuccess_1675_,
        v_cerror_1676_,
        v_it_1677_,
    );
    crate::leanh::lean_dec_ref(v_inst_1671_);
    return v_res_1678_;
}
pub unsafe fn l_Std_Internal_Parsec_instMonad___lam__0(
    mut v_00_u03b1_1679_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_1680_: *mut crate::leanh::LeanObject,
    mut v_f_1681_: *mut crate::leanh::LeanObject,
    mut v_x_1682_: *mut crate::leanh::LeanObject,
    mut v___y_1683_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1684_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_pos_1685_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_res_1686_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1688_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1689_: u8 = 0;
    let mut v___x_1690_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1692_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1693_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1694_: u8 = 0;
    let mut v_pos_1695_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_err_1696_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1698_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1699_: u8 = 0;
    let mut v___x_1701_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1702_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1703_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1684_ = crate::leanh::lean_apply_1(v_x_1682_, v___y_1683_);
                if crate::leanh::lean_obj_tag(v___x_1684_) == 0 {
                    v_pos_1685_ = crate::leanh::lean_ctor_get(v___x_1684_, 0);
                    v_res_1686_ = crate::leanh::lean_ctor_get(v___x_1684_, 1);
                    v_isSharedCheck_1694_ = (!crate::leanh::lean_is_exclusive(v___x_1684_)) as u8;
                    if v_isSharedCheck_1694_ == 0 {
                        v___x_1688_ = v___x_1684_;
                        v_isShared_1689_ = v_isSharedCheck_1694_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_res_1686_);
                        crate::leanh::lean_inc(v_pos_1685_);
                        crate::leanh::lean_dec(v___x_1684_);
                        v___x_1688_ = crate::leanh::lean_box(0);
                        v_isShared_1689_ = v_isSharedCheck_1694_;
                        state = 1;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_f_1681_);
                    v_pos_1695_ = crate::leanh::lean_ctor_get(v___x_1684_, 0);
                    v_err_1696_ = crate::leanh::lean_ctor_get(v___x_1684_, 1);
                    v_isSharedCheck_1703_ = (!crate::leanh::lean_is_exclusive(v___x_1684_)) as u8;
                    if v_isSharedCheck_1703_ == 0 {
                        v___x_1698_ = v___x_1684_;
                        v_isShared_1699_ = v_isSharedCheck_1703_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_err_1696_);
                        crate::leanh::lean_inc(v_pos_1695_);
                        crate::leanh::lean_dec(v___x_1684_);
                        v___x_1698_ = crate::leanh::lean_box(0);
                        v_isShared_1699_ = v_isSharedCheck_1703_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v___x_1690_ = crate::leanh::lean_apply_1(v_f_1681_, v_res_1686_);
                if v_isShared_1689_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1688_, 1, v___x_1690_);
                    v___x_1692_ = v___x_1688_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1693_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1693_, 0, v_pos_1685_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1693_, 1, v___x_1690_);
                    v___x_1692_ = v_reuseFailAlloc_1693_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1692_;
            }
            3 => {
                if v_isShared_1699_ == 0 {
                    v___x_1701_ = v___x_1698_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1702_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1702_, 0, v_pos_1695_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1702_, 1, v_err_1696_);
                    v___x_1701_ = v_reuseFailAlloc_1702_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_1701_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Internal_Parsec_instMonad___lam__1(
    mut v_00_u03b1_1704_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_1705_: *mut crate::leanh::LeanObject,
    mut v___y_1706_: *mut crate::leanh::LeanObject,
    mut v___y_1707_: *mut crate::leanh::LeanObject,
    mut v___y_1708_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1709_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_pos_1710_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1712_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1713_: u8 = 0;
    let mut v___x_1715_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1716_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1717_: u8 = 0;
    let mut v_unused_1718_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_pos_1719_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_err_1720_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1722_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1723_: u8 = 0;
    let mut v___x_1725_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1726_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1727_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1709_ = crate::leanh::lean_apply_1(v___y_1707_, v___y_1708_);
                if crate::leanh::lean_obj_tag(v___x_1709_) == 0 {
                    v_pos_1710_ = crate::leanh::lean_ctor_get(v___x_1709_, 0);
                    v_isSharedCheck_1717_ = (!crate::leanh::lean_is_exclusive(v___x_1709_)) as u8;
                    if v_isSharedCheck_1717_ == 0 {
                        v_unused_1718_ = crate::leanh::lean_ctor_get(v___x_1709_, 1);
                        crate::leanh::lean_dec(v_unused_1718_);
                        v___x_1712_ = v___x_1709_;
                        v_isShared_1713_ = v_isSharedCheck_1717_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_pos_1710_);
                        crate::leanh::lean_dec(v___x_1709_);
                        v___x_1712_ = crate::leanh::lean_box(0);
                        v_isShared_1713_ = v_isSharedCheck_1717_;
                        state = 1;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v___y_1706_);
                    v_pos_1719_ = crate::leanh::lean_ctor_get(v___x_1709_, 0);
                    v_err_1720_ = crate::leanh::lean_ctor_get(v___x_1709_, 1);
                    v_isSharedCheck_1727_ = (!crate::leanh::lean_is_exclusive(v___x_1709_)) as u8;
                    if v_isSharedCheck_1727_ == 0 {
                        v___x_1722_ = v___x_1709_;
                        v_isShared_1723_ = v_isSharedCheck_1727_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_err_1720_);
                        crate::leanh::lean_inc(v_pos_1719_);
                        crate::leanh::lean_dec(v___x_1709_);
                        v___x_1722_ = crate::leanh::lean_box(0);
                        v_isShared_1723_ = v_isSharedCheck_1727_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_1713_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1712_, 1, v___y_1706_);
                    v___x_1715_ = v___x_1712_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1716_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1716_, 0, v_pos_1710_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1716_, 1, v___y_1706_);
                    v___x_1715_ = v_reuseFailAlloc_1716_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1715_;
            }
            3 => {
                if v_isShared_1723_ == 0 {
                    v___x_1725_ = v___x_1722_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1726_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1726_, 0, v_pos_1719_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1726_, 1, v_err_1720_);
                    v___x_1725_ = v_reuseFailAlloc_1726_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_1725_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Internal_Parsec_instMonad___lam__2(
    mut v_00_u03b1_1728_: *mut crate::leanh::LeanObject,
    mut v___y_1729_: *mut crate::leanh::LeanObject,
    mut v___y_1730_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1731_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1731_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1731_, 0, v___y_1730_);
    crate::leanh::lean_ctor_set(v___x_1731_, 1, v___y_1729_);
    return v___x_1731_;
}
pub unsafe fn l_Std_Internal_Parsec_instMonad___lam__3(
    mut v_00_u03b1_1732_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_1733_: *mut crate::leanh::LeanObject,
    mut v_f_1734_: *mut crate::leanh::LeanObject,
    mut v_x_1735_: *mut crate::leanh::LeanObject,
    mut v___y_1736_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1737_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_pos_1738_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_res_1739_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1740_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1741_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_pos_1742_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_res_1743_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1745_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1746_: u8 = 0;
    let mut v___x_1747_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1749_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1750_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1751_: u8 = 0;
    let mut v_pos_1752_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_err_1753_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1755_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1756_: u8 = 0;
    let mut v___x_1758_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1759_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1760_: u8 = 0;
    let mut v_pos_1761_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_err_1762_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1764_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1765_: u8 = 0;
    let mut v___x_1767_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1768_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1769_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1737_ = crate::leanh::lean_apply_1(v_f_1734_, v___y_1736_);
                if crate::leanh::lean_obj_tag(v___x_1737_) == 0 {
                    v_pos_1738_ = crate::leanh::lean_ctor_get(v___x_1737_, 0);
                    crate::leanh::lean_inc(v_pos_1738_);
                    v_res_1739_ = crate::leanh::lean_ctor_get(v___x_1737_, 1);
                    crate::leanh::lean_inc(v_res_1739_);
                    crate::leanh::lean_dec_ref_known(v___x_1737_, 2);
                    v___x_1740_ = crate::leanh::lean_box(0);
                    v___x_1741_ = crate::leanh::lean_apply_2(v_x_1735_, v___x_1740_, v_pos_1738_);
                    if crate::leanh::lean_obj_tag(v___x_1741_) == 0 {
                        v_pos_1742_ = crate::leanh::lean_ctor_get(v___x_1741_, 0);
                        v_res_1743_ = crate::leanh::lean_ctor_get(v___x_1741_, 1);
                        v_isSharedCheck_1751_ =
                            (!crate::leanh::lean_is_exclusive(v___x_1741_)) as u8;
                        if v_isSharedCheck_1751_ == 0 {
                            v___x_1745_ = v___x_1741_;
                            v_isShared_1746_ = v_isSharedCheck_1751_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_res_1743_);
                            crate::leanh::lean_inc(v_pos_1742_);
                            crate::leanh::lean_dec(v___x_1741_);
                            v___x_1745_ = crate::leanh::lean_box(0);
                            v_isShared_1746_ = v_isSharedCheck_1751_;
                            state = 1;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec(v_res_1739_);
                        v_pos_1752_ = crate::leanh::lean_ctor_get(v___x_1741_, 0);
                        v_err_1753_ = crate::leanh::lean_ctor_get(v___x_1741_, 1);
                        v_isSharedCheck_1760_ =
                            (!crate::leanh::lean_is_exclusive(v___x_1741_)) as u8;
                        if v_isSharedCheck_1760_ == 0 {
                            v___x_1755_ = v___x_1741_;
                            v_isShared_1756_ = v_isSharedCheck_1760_;
                            state = 3;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_err_1753_);
                            crate::leanh::lean_inc(v_pos_1752_);
                            crate::leanh::lean_dec(v___x_1741_);
                            v___x_1755_ = crate::leanh::lean_box(0);
                            v_isShared_1756_ = v_isSharedCheck_1760_;
                            state = 3;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_x_1735_);
                    v_pos_1761_ = crate::leanh::lean_ctor_get(v___x_1737_, 0);
                    v_err_1762_ = crate::leanh::lean_ctor_get(v___x_1737_, 1);
                    v_isSharedCheck_1769_ = (!crate::leanh::lean_is_exclusive(v___x_1737_)) as u8;
                    if v_isSharedCheck_1769_ == 0 {
                        v___x_1764_ = v___x_1737_;
                        v_isShared_1765_ = v_isSharedCheck_1769_;
                        state = 5;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_err_1762_);
                        crate::leanh::lean_inc(v_pos_1761_);
                        crate::leanh::lean_dec(v___x_1737_);
                        v___x_1764_ = crate::leanh::lean_box(0);
                        v_isShared_1765_ = v_isSharedCheck_1769_;
                        state = 5;
                        continue;
                    }
                }
            }
            1 => {
                v___x_1747_ = crate::leanh::lean_apply_1(v_res_1739_, v_res_1743_);
                if v_isShared_1746_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1745_, 1, v___x_1747_);
                    v___x_1749_ = v___x_1745_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1750_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1750_, 0, v_pos_1742_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1750_, 1, v___x_1747_);
                    v___x_1749_ = v_reuseFailAlloc_1750_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1749_;
            }
            3 => {
                if v_isShared_1756_ == 0 {
                    v___x_1758_ = v___x_1755_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1759_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1759_, 0, v_pos_1752_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1759_, 1, v_err_1753_);
                    v___x_1758_ = v_reuseFailAlloc_1759_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_1758_;
            }
            5 => {
                if v_isShared_1765_ == 0 {
                    v___x_1767_ = v___x_1764_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_1768_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1768_, 0, v_pos_1761_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1768_, 1, v_err_1762_);
                    v___x_1767_ = v_reuseFailAlloc_1768_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_1767_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Internal_Parsec_instMonad___lam__4(
    mut v_00_u03b1_1770_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_1771_: *mut crate::leanh::LeanObject,
    mut v_x_1772_: *mut crate::leanh::LeanObject,
    mut v_y_1773_: *mut crate::leanh::LeanObject,
    mut v___y_1774_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1775_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_pos_1776_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_res_1777_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1778_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1779_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_pos_1780_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1782_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1783_: u8 = 0;
    let mut v___x_1785_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1786_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1787_: u8 = 0;
    let mut v_unused_1788_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_pos_1789_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_err_1790_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1792_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1793_: u8 = 0;
    let mut v___x_1795_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1796_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1797_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1775_ = crate::leanh::lean_apply_1(v_x_1772_, v___y_1774_);
                if crate::leanh::lean_obj_tag(v___x_1775_) == 0 {
                    v_pos_1776_ = crate::leanh::lean_ctor_get(v___x_1775_, 0);
                    crate::leanh::lean_inc(v_pos_1776_);
                    v_res_1777_ = crate::leanh::lean_ctor_get(v___x_1775_, 1);
                    crate::leanh::lean_inc(v_res_1777_);
                    crate::leanh::lean_dec_ref_known(v___x_1775_, 2);
                    v___x_1778_ = crate::leanh::lean_box(0);
                    v___x_1779_ = crate::leanh::lean_apply_2(v_y_1773_, v___x_1778_, v_pos_1776_);
                    if crate::leanh::lean_obj_tag(v___x_1779_) == 0 {
                        v_pos_1780_ = crate::leanh::lean_ctor_get(v___x_1779_, 0);
                        v_isSharedCheck_1787_ =
                            (!crate::leanh::lean_is_exclusive(v___x_1779_)) as u8;
                        if v_isSharedCheck_1787_ == 0 {
                            v_unused_1788_ = crate::leanh::lean_ctor_get(v___x_1779_, 1);
                            crate::leanh::lean_dec(v_unused_1788_);
                            v___x_1782_ = v___x_1779_;
                            v_isShared_1783_ = v_isSharedCheck_1787_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_pos_1780_);
                            crate::leanh::lean_dec(v___x_1779_);
                            v___x_1782_ = crate::leanh::lean_box(0);
                            v_isShared_1783_ = v_isSharedCheck_1787_;
                            state = 1;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec(v_res_1777_);
                        v_pos_1789_ = crate::leanh::lean_ctor_get(v___x_1779_, 0);
                        v_err_1790_ = crate::leanh::lean_ctor_get(v___x_1779_, 1);
                        v_isSharedCheck_1797_ =
                            (!crate::leanh::lean_is_exclusive(v___x_1779_)) as u8;
                        if v_isSharedCheck_1797_ == 0 {
                            v___x_1792_ = v___x_1779_;
                            v_isShared_1793_ = v_isSharedCheck_1797_;
                            state = 3;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_err_1790_);
                            crate::leanh::lean_inc(v_pos_1789_);
                            crate::leanh::lean_dec(v___x_1779_);
                            v___x_1792_ = crate::leanh::lean_box(0);
                            v_isShared_1793_ = v_isSharedCheck_1797_;
                            state = 3;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_y_1773_);
                    return v___x_1775_;
                }
            }
            1 => {
                if v_isShared_1783_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1782_, 1, v_res_1777_);
                    v___x_1785_ = v___x_1782_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1786_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1786_, 0, v_pos_1780_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1786_, 1, v_res_1777_);
                    v___x_1785_ = v_reuseFailAlloc_1786_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1785_;
            }
            3 => {
                if v_isShared_1793_ == 0 {
                    v___x_1795_ = v___x_1792_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1796_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1796_, 0, v_pos_1789_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1796_, 1, v_err_1790_);
                    v___x_1795_ = v_reuseFailAlloc_1796_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_1795_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Internal_Parsec_instMonad___lam__5(
    mut v_00_u03b1_1798_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_1799_: *mut crate::leanh::LeanObject,
    mut v_x_1800_: *mut crate::leanh::LeanObject,
    mut v_y_1801_: *mut crate::leanh::LeanObject,
    mut v___y_1802_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1803_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_pos_1804_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1805_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1806_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_pos_1807_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_err_1808_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1810_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1811_: u8 = 0;
    let mut v___x_1813_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1814_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1815_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1803_ = crate::leanh::lean_apply_1(v_x_1800_, v___y_1802_);
                if crate::leanh::lean_obj_tag(v___x_1803_) == 0 {
                    v_pos_1804_ = crate::leanh::lean_ctor_get(v___x_1803_, 0);
                    crate::leanh::lean_inc(v_pos_1804_);
                    crate::leanh::lean_dec_ref_known(v___x_1803_, 2);
                    v___x_1805_ = crate::leanh::lean_box(0);
                    v___x_1806_ = crate::leanh::lean_apply_2(v_y_1801_, v___x_1805_, v_pos_1804_);
                    return v___x_1806_;
                } else {
                    crate::leanh::lean_dec_ref(v_y_1801_);
                    v_pos_1807_ = crate::leanh::lean_ctor_get(v___x_1803_, 0);
                    v_err_1808_ = crate::leanh::lean_ctor_get(v___x_1803_, 1);
                    v_isSharedCheck_1815_ = (!crate::leanh::lean_is_exclusive(v___x_1803_)) as u8;
                    if v_isSharedCheck_1815_ == 0 {
                        v___x_1810_ = v___x_1803_;
                        v_isShared_1811_ = v_isSharedCheck_1815_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_err_1808_);
                        crate::leanh::lean_inc(v_pos_1807_);
                        crate::leanh::lean_dec(v___x_1803_);
                        v___x_1810_ = crate::leanh::lean_box(0);
                        v_isShared_1811_ = v_isSharedCheck_1815_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_1811_ == 0 {
                    v___x_1813_ = v___x_1810_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1814_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1814_, 0, v_pos_1807_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1814_, 1, v_err_1808_);
                    v___x_1813_ = v_reuseFailAlloc_1814_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1813_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Internal_Parsec_instMonad(
    mut v_00_u03b9_1835_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1836_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1836_ = l_Std_Internal_Parsec_instMonad___closed__9;
    return v___x_1836_;
}
pub unsafe fn l_Std_Internal_Parsec_orElse___redArg(
    mut v_inst_1837_: *mut crate::leanh::LeanObject,
    mut v_inst_1838_: *mut crate::leanh::LeanObject,
    mut v_p_1839_: *mut crate::leanh::LeanObject,
    mut v_q_1840_: *mut crate::leanh::LeanObject,
    mut v_a_1841_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1842_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    crate::leanh::lean_inc(v_a_1841_);
    v___x_1842_ = crate::leanh::lean_apply_1(v_p_1839_, v_a_1841_);
    if crate::leanh::lean_obj_tag(v___x_1842_) == 0 {
        crate::leanh::lean_dec(v_a_1841_);
        crate::leanh::lean_dec_ref(v_q_1840_);
        crate::leanh::lean_dec_ref(v_inst_1838_);
        crate::leanh::lean_dec_ref(v_inst_1837_);
        return v___x_1842_;
    } else {
        let mut v_pos_1843_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_pos_1844_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1845_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1846_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1847_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1848_: u8 = 0;
        v_pos_1843_ = crate::leanh::lean_ctor_get(v___x_1842_, 0);
        crate::leanh::lean_inc_n(v_pos_1843_, 2);
        v_pos_1844_ = crate::leanh::lean_ctor_get(v_inst_1838_, 0);
        crate::leanh::lean_inc_n(v_pos_1844_, 2);
        crate::leanh::lean_dec_ref(v_inst_1838_);
        v___x_1845_ = crate::leanh::lean_apply_1(v_pos_1844_, v_a_1841_);
        v___x_1846_ = crate::leanh::lean_apply_1(v_pos_1844_, v_pos_1843_);
        v___x_1847_ = crate::leanh::lean_apply_2(v_inst_1837_, v___x_1845_, v___x_1846_);
        v___x_1848_ = (crate::leanh::lean_unbox(v___x_1847_) as u8);
        if v___x_1848_ == 0 {
            crate::leanh::lean_dec(v_pos_1843_);
            crate::leanh::lean_dec_ref(v_q_1840_);
            return v___x_1842_;
        } else {
            let mut v___x_1849_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1850_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec_ref_known(v___x_1842_, 2);
            v___x_1849_ = crate::leanh::lean_box(0);
            v___x_1850_ = crate::leanh::lean_apply_2(v_q_1840_, v___x_1849_, v_pos_1843_);
            return v___x_1850_;
        }
    }
}
pub unsafe fn l_Std_Internal_Parsec_orElse(
    mut v_00_u03b1_1851_: *mut crate::leanh::LeanObject,
    mut v_00_u03b9_1852_: *mut crate::leanh::LeanObject,
    mut v_elem_1853_: *mut crate::leanh::LeanObject,
    mut v_idx_1854_: *mut crate::leanh::LeanObject,
    mut v_inst_1855_: *mut crate::leanh::LeanObject,
    mut v_inst_1856_: *mut crate::leanh::LeanObject,
    mut v_inst_1857_: *mut crate::leanh::LeanObject,
    mut v_p_1858_: *mut crate::leanh::LeanObject,
    mut v_q_1859_: *mut crate::leanh::LeanObject,
    mut v_a_1860_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1861_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    crate::leanh::lean_inc(v_a_1860_);
    v___x_1861_ = crate::leanh::lean_apply_1(v_p_1858_, v_a_1860_);
    if crate::leanh::lean_obj_tag(v___x_1861_) == 0 {
        crate::leanh::lean_dec(v_a_1860_);
        crate::leanh::lean_dec_ref(v_q_1859_);
        crate::leanh::lean_dec_ref(v_inst_1857_);
        crate::leanh::lean_dec_ref(v_inst_1855_);
        return v___x_1861_;
    } else {
        let mut v_pos_1862_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_pos_1863_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1864_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1865_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1866_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1867_: u8 = 0;
        v_pos_1862_ = crate::leanh::lean_ctor_get(v___x_1861_, 0);
        crate::leanh::lean_inc_n(v_pos_1862_, 2);
        v_pos_1863_ = crate::leanh::lean_ctor_get(v_inst_1857_, 0);
        crate::leanh::lean_inc_n(v_pos_1863_, 2);
        crate::leanh::lean_dec_ref(v_inst_1857_);
        v___x_1864_ = crate::leanh::lean_apply_1(v_pos_1863_, v_a_1860_);
        v___x_1865_ = crate::leanh::lean_apply_1(v_pos_1863_, v_pos_1862_);
        v___x_1866_ = crate::leanh::lean_apply_2(v_inst_1855_, v___x_1864_, v___x_1865_);
        v___x_1867_ = (crate::leanh::lean_unbox(v___x_1866_) as u8);
        if v___x_1867_ == 0 {
            crate::leanh::lean_dec(v_pos_1862_);
            crate::leanh::lean_dec_ref(v_q_1859_);
            return v___x_1861_;
        } else {
            let mut v___x_1868_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1869_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec_ref_known(v___x_1861_, 2);
            v___x_1868_ = crate::leanh::lean_box(0);
            v___x_1869_ = crate::leanh::lean_apply_2(v_q_1859_, v___x_1868_, v_pos_1862_);
            return v___x_1869_;
        }
    }
}
pub unsafe fn l_Std_Internal_Parsec_orElse___boxed(
    mut v_00_u03b1_1870_: *mut crate::leanh::LeanObject,
    mut v_00_u03b9_1871_: *mut crate::leanh::LeanObject,
    mut v_elem_1872_: *mut crate::leanh::LeanObject,
    mut v_idx_1873_: *mut crate::leanh::LeanObject,
    mut v_inst_1874_: *mut crate::leanh::LeanObject,
    mut v_inst_1875_: *mut crate::leanh::LeanObject,
    mut v_inst_1876_: *mut crate::leanh::LeanObject,
    mut v_p_1877_: *mut crate::leanh::LeanObject,
    mut v_q_1878_: *mut crate::leanh::LeanObject,
    mut v_a_1879_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1880_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1880_ = l_Std_Internal_Parsec_orElse(
        v_00_u03b1_1870_,
        v_00_u03b9_1871_,
        v_elem_1872_,
        v_idx_1873_,
        v_inst_1874_,
        v_inst_1875_,
        v_inst_1876_,
        v_p_1877_,
        v_q_1878_,
        v_a_1879_,
    );
    crate::leanh::lean_dec_ref(v_inst_1875_);
    return v_res_1880_;
}
pub unsafe fn l_Std_Internal_Parsec_attempt___redArg(
    mut v_p_1881_: *mut crate::leanh::LeanObject,
    mut v_it_1882_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1883_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_err_1884_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1886_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1887_: u8 = 0;
    let mut v___x_1889_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1890_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1891_: u8 = 0;
    let mut v_unused_1892_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                crate::leanh::lean_inc(v_it_1882_);
                v___x_1883_ = crate::leanh::lean_apply_1(v_p_1881_, v_it_1882_);
                if crate::leanh::lean_obj_tag(v___x_1883_) == 0 {
                    crate::leanh::lean_dec(v_it_1882_);
                    return v___x_1883_;
                } else {
                    v_err_1884_ = crate::leanh::lean_ctor_get(v___x_1883_, 1);
                    v_isSharedCheck_1891_ = (!crate::leanh::lean_is_exclusive(v___x_1883_)) as u8;
                    if v_isSharedCheck_1891_ == 0 {
                        v_unused_1892_ = crate::leanh::lean_ctor_get(v___x_1883_, 0);
                        crate::leanh::lean_dec(v_unused_1892_);
                        v___x_1886_ = v___x_1883_;
                        v_isShared_1887_ = v_isSharedCheck_1891_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_err_1884_);
                        crate::leanh::lean_dec(v___x_1883_);
                        v___x_1886_ = crate::leanh::lean_box(0);
                        v_isShared_1887_ = v_isSharedCheck_1891_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_1887_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1886_, 0, v_it_1882_);
                    v___x_1889_ = v___x_1886_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1890_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1890_, 0, v_it_1882_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1890_, 1, v_err_1884_);
                    v___x_1889_ = v_reuseFailAlloc_1890_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1889_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Internal_Parsec_attempt(
    mut v_00_u03b1_1893_: *mut crate::leanh::LeanObject,
    mut v_00_u03b9_1894_: *mut crate::leanh::LeanObject,
    mut v_p_1895_: *mut crate::leanh::LeanObject,
    mut v_it_1896_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1897_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_err_1898_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1900_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1901_: u8 = 0;
    let mut v___x_1903_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1904_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1905_: u8 = 0;
    let mut v_unused_1906_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                crate::leanh::lean_inc(v_it_1896_);
                v___x_1897_ = crate::leanh::lean_apply_1(v_p_1895_, v_it_1896_);
                if crate::leanh::lean_obj_tag(v___x_1897_) == 0 {
                    crate::leanh::lean_dec(v_it_1896_);
                    return v___x_1897_;
                } else {
                    v_err_1898_ = crate::leanh::lean_ctor_get(v___x_1897_, 1);
                    v_isSharedCheck_1905_ = (!crate::leanh::lean_is_exclusive(v___x_1897_)) as u8;
                    if v_isSharedCheck_1905_ == 0 {
                        v_unused_1906_ = crate::leanh::lean_ctor_get(v___x_1897_, 0);
                        crate::leanh::lean_dec(v_unused_1906_);
                        v___x_1900_ = v___x_1897_;
                        v_isShared_1901_ = v_isSharedCheck_1905_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_err_1898_);
                        crate::leanh::lean_dec(v___x_1897_);
                        v___x_1900_ = crate::leanh::lean_box(0);
                        v_isShared_1901_ = v_isSharedCheck_1905_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_1901_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1900_, 0, v_it_1896_);
                    v___x_1903_ = v___x_1900_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1904_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1904_, 0, v_it_1896_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1904_, 1, v_err_1898_);
                    v___x_1903_ = v_reuseFailAlloc_1904_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1903_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Internal_Parsec_instAlternative___redArg___lam__0(
    mut v_00_u03b1_1907_: *mut crate::leanh::LeanObject,
    mut v___y_1908_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1909_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1910_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1909_ = l_Std_Internal_Parsec_instInhabited___lam__0___closed__1;
    v___x_1910_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1910_, 0, v___y_1908_);
    crate::leanh::lean_ctor_set(v___x_1910_, 1, v___x_1909_);
    return v___x_1910_;
}
pub unsafe fn l_Std_Internal_Parsec_instAlternative___redArg___lam__1(
    mut v_inst_1911_: *mut crate::leanh::LeanObject,
    mut v_inst_1912_: *mut crate::leanh::LeanObject,
    mut v_00_u03b1_1913_: *mut crate::leanh::LeanObject,
    mut v___y_1914_: *mut crate::leanh::LeanObject,
    mut v___y_1915_: *mut crate::leanh::LeanObject,
    mut v___y_1916_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1917_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    crate::leanh::lean_inc(v___y_1916_);
    v___x_1917_ = crate::leanh::lean_apply_1(v___y_1914_, v___y_1916_);
    if crate::leanh::lean_obj_tag(v___x_1917_) == 0 {
        crate::leanh::lean_dec(v___y_1916_);
        crate::leanh::lean_dec_ref(v___y_1915_);
        crate::leanh::lean_dec_ref(v_inst_1912_);
        crate::leanh::lean_dec_ref(v_inst_1911_);
        return v___x_1917_;
    } else {
        let mut v_pos_1918_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_pos_1919_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1920_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1921_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1922_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1923_: u8 = 0;
        v_pos_1918_ = crate::leanh::lean_ctor_get(v___x_1917_, 0);
        crate::leanh::lean_inc_n(v_pos_1918_, 2);
        v_pos_1919_ = crate::leanh::lean_ctor_get(v_inst_1911_, 0);
        crate::leanh::lean_inc_n(v_pos_1919_, 2);
        crate::leanh::lean_dec_ref(v_inst_1911_);
        v___x_1920_ = crate::leanh::lean_apply_1(v_pos_1919_, v___y_1916_);
        v___x_1921_ = crate::leanh::lean_apply_1(v_pos_1919_, v_pos_1918_);
        v___x_1922_ = crate::leanh::lean_apply_2(v_inst_1912_, v___x_1920_, v___x_1921_);
        v___x_1923_ = (crate::leanh::lean_unbox(v___x_1922_) as u8);
        if v___x_1923_ == 0 {
            crate::leanh::lean_dec(v_pos_1918_);
            crate::leanh::lean_dec_ref(v___y_1915_);
            return v___x_1917_;
        } else {
            let mut v___x_1924_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1925_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec_ref_known(v___x_1917_, 2);
            v___x_1924_ = crate::leanh::lean_box(0);
            v___x_1925_ = crate::leanh::lean_apply_2(v___y_1915_, v___x_1924_, v_pos_1918_);
            return v___x_1925_;
        }
    }
}
pub unsafe fn l_Std_Internal_Parsec_instAlternative___redArg(
    mut v_inst_1927_: *mut crate::leanh::LeanObject,
    mut v_inst_1928_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_1929_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1930_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1931_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1932_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_1929_ = l_Std_Internal_Parsec_instAlternative___redArg___closed__0;
    v___f_1930_ = crate::leanh::lean_alloc_closure(
        l_Std_Internal_Parsec_instAlternative___redArg___lam__1 as *mut core::ffi::c_void,
        6,
        2,
    );
    crate::leanh::lean_closure_set(v___f_1930_, 0, v_inst_1928_);
    crate::leanh::lean_closure_set(v___f_1930_, 1, v_inst_1927_);
    v___x_1931_ = l_Std_Internal_Parsec_instMonad___closed__7;
    v___x_1932_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1932_, 0, v___x_1931_);
    crate::leanh::lean_ctor_set(v___x_1932_, 1, v___f_1929_);
    crate::leanh::lean_ctor_set(v___x_1932_, 2, v___f_1930_);
    return v___x_1932_;
}
pub unsafe fn l_Std_Internal_Parsec_instAlternative(
    mut v_00_u03b9_1933_: *mut crate::leanh::LeanObject,
    mut v_elem_1934_: *mut crate::leanh::LeanObject,
    mut v_idx_1935_: *mut crate::leanh::LeanObject,
    mut v_inst_1936_: *mut crate::leanh::LeanObject,
    mut v_inst_1937_: *mut crate::leanh::LeanObject,
    mut v_inst_1938_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_1939_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1940_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1941_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1942_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_1939_ = l_Std_Internal_Parsec_instAlternative___redArg___closed__0;
    v___f_1940_ = crate::leanh::lean_alloc_closure(
        l_Std_Internal_Parsec_instAlternative___redArg___lam__1 as *mut core::ffi::c_void,
        6,
        2,
    );
    crate::leanh::lean_closure_set(v___f_1940_, 0, v_inst_1938_);
    crate::leanh::lean_closure_set(v___f_1940_, 1, v_inst_1936_);
    v___x_1941_ = l_Std_Internal_Parsec_instMonad___closed__7;
    v___x_1942_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1942_, 0, v___x_1941_);
    crate::leanh::lean_ctor_set(v___x_1942_, 1, v___f_1939_);
    crate::leanh::lean_ctor_set(v___x_1942_, 2, v___f_1940_);
    return v___x_1942_;
}
pub unsafe fn l_Std_Internal_Parsec_instAlternative___boxed(
    mut v_00_u03b9_1943_: *mut crate::leanh::LeanObject,
    mut v_elem_1944_: *mut crate::leanh::LeanObject,
    mut v_idx_1945_: *mut crate::leanh::LeanObject,
    mut v_inst_1946_: *mut crate::leanh::LeanObject,
    mut v_inst_1947_: *mut crate::leanh::LeanObject,
    mut v_inst_1948_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1949_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1949_ = l_Std_Internal_Parsec_instAlternative(
        v_00_u03b9_1943_,
        v_elem_1944_,
        v_idx_1945_,
        v_inst_1946_,
        v_inst_1947_,
        v_inst_1948_,
    );
    crate::leanh::lean_dec_ref(v_inst_1947_);
    return v_res_1949_;
}
pub unsafe fn l_Std_Internal_Parsec_eof___redArg(
    mut v_inst_1953_: *mut crate::leanh::LeanObject,
    mut v_it_1954_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_hasNext_1955_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1956_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1957_: u8 = 0;
    v_hasNext_1955_ = crate::leanh::lean_ctor_get(v_inst_1953_, 3);
    crate::leanh::lean_inc_ref(v_hasNext_1955_);
    crate::leanh::lean_dec_ref(v_inst_1953_);
    crate::leanh::lean_inc(v_it_1954_);
    v___x_1956_ = crate::leanh::lean_apply_1(v_hasNext_1955_, v_it_1954_);
    v___x_1957_ = (crate::leanh::lean_unbox(v___x_1956_) as u8);
    if v___x_1957_ == 0 {
        let mut v___x_1958_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1959_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_1958_ = crate::leanh::lean_box(0);
        v___x_1959_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_1959_, 0, v_it_1954_);
        crate::leanh::lean_ctor_set(v___x_1959_, 1, v___x_1958_);
        return v___x_1959_;
    } else {
        let mut v___x_1960_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1961_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_1960_ = l_Std_Internal_Parsec_eof___redArg___closed__1;
        v___x_1961_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_1961_, 0, v_it_1954_);
        crate::leanh::lean_ctor_set(v___x_1961_, 1, v___x_1960_);
        return v___x_1961_;
    }
}
pub unsafe fn l_Std_Internal_Parsec_eof(
    mut v_00_u03b9_1962_: *mut crate::leanh::LeanObject,
    mut v_elem_1963_: *mut crate::leanh::LeanObject,
    mut v_idx_1964_: *mut crate::leanh::LeanObject,
    mut v_inst_1965_: *mut crate::leanh::LeanObject,
    mut v_inst_1966_: *mut crate::leanh::LeanObject,
    mut v_inst_1967_: *mut crate::leanh::LeanObject,
    mut v_it_1968_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_hasNext_1969_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1970_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1971_: u8 = 0;
    v_hasNext_1969_ = crate::leanh::lean_ctor_get(v_inst_1967_, 3);
    crate::leanh::lean_inc_ref(v_hasNext_1969_);
    crate::leanh::lean_dec_ref(v_inst_1967_);
    crate::leanh::lean_inc(v_it_1968_);
    v___x_1970_ = crate::leanh::lean_apply_1(v_hasNext_1969_, v_it_1968_);
    v___x_1971_ = (crate::leanh::lean_unbox(v___x_1970_) as u8);
    if v___x_1971_ == 0 {
        let mut v___x_1972_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1973_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_1972_ = crate::leanh::lean_box(0);
        v___x_1973_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_1973_, 0, v_it_1968_);
        crate::leanh::lean_ctor_set(v___x_1973_, 1, v___x_1972_);
        return v___x_1973_;
    } else {
        let mut v___x_1974_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1975_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_1974_ = l_Std_Internal_Parsec_eof___redArg___closed__1;
        v___x_1975_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_1975_, 0, v_it_1968_);
        crate::leanh::lean_ctor_set(v___x_1975_, 1, v___x_1974_);
        return v___x_1975_;
    }
}
pub unsafe fn l_Std_Internal_Parsec_eof___boxed(
    mut v_00_u03b9_1976_: *mut crate::leanh::LeanObject,
    mut v_elem_1977_: *mut crate::leanh::LeanObject,
    mut v_idx_1978_: *mut crate::leanh::LeanObject,
    mut v_inst_1979_: *mut crate::leanh::LeanObject,
    mut v_inst_1980_: *mut crate::leanh::LeanObject,
    mut v_inst_1981_: *mut crate::leanh::LeanObject,
    mut v_it_1982_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1983_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1983_ = l_Std_Internal_Parsec_eof(
        v_00_u03b9_1976_,
        v_elem_1977_,
        v_idx_1978_,
        v_inst_1979_,
        v_inst_1980_,
        v_inst_1981_,
        v_it_1982_,
    );
    crate::leanh::lean_dec_ref(v_inst_1980_);
    crate::leanh::lean_dec_ref(v_inst_1979_);
    return v_res_1983_;
}
pub unsafe fn l_Std_Internal_Parsec_isEof___redArg(
    mut v_inst_1984_: *mut crate::leanh::LeanObject,
    mut v_it_1985_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_hasNext_1986_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1987_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1988_: u8 = 0;
    v_hasNext_1986_ = crate::leanh::lean_ctor_get(v_inst_1984_, 3);
    crate::leanh::lean_inc_ref(v_hasNext_1986_);
    crate::leanh::lean_dec_ref(v_inst_1984_);
    crate::leanh::lean_inc(v_it_1985_);
    v___x_1987_ = crate::leanh::lean_apply_1(v_hasNext_1986_, v_it_1985_);
    v___x_1988_ = (crate::leanh::lean_unbox(v___x_1987_) as u8);
    if v___x_1988_ == 0 {
        let mut v___x_1989_: u8 = 0;
        let mut v___x_1990_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1991_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_1989_ = 1;
        v___x_1990_ = crate::leanh::lean_box((v___x_1989_) as usize);
        v___x_1991_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_1991_, 0, v_it_1985_);
        crate::leanh::lean_ctor_set(v___x_1991_, 1, v___x_1990_);
        return v___x_1991_;
    } else {
        let mut v___x_1992_: u8 = 0;
        let mut v___x_1993_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1994_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_1992_ = 0;
        v___x_1993_ = crate::leanh::lean_box((v___x_1992_) as usize);
        v___x_1994_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_1994_, 0, v_it_1985_);
        crate::leanh::lean_ctor_set(v___x_1994_, 1, v___x_1993_);
        return v___x_1994_;
    }
}
pub unsafe fn l_Std_Internal_Parsec_isEof(
    mut v_00_u03b9_1995_: *mut crate::leanh::LeanObject,
    mut v_elem_1996_: *mut crate::leanh::LeanObject,
    mut v_idx_1997_: *mut crate::leanh::LeanObject,
    mut v_inst_1998_: *mut crate::leanh::LeanObject,
    mut v_inst_1999_: *mut crate::leanh::LeanObject,
    mut v_inst_2000_: *mut crate::leanh::LeanObject,
    mut v_it_2001_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_hasNext_2002_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2003_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2004_: u8 = 0;
    v_hasNext_2002_ = crate::leanh::lean_ctor_get(v_inst_2000_, 3);
    crate::leanh::lean_inc_ref(v_hasNext_2002_);
    crate::leanh::lean_dec_ref(v_inst_2000_);
    crate::leanh::lean_inc(v_it_2001_);
    v___x_2003_ = crate::leanh::lean_apply_1(v_hasNext_2002_, v_it_2001_);
    v___x_2004_ = (crate::leanh::lean_unbox(v___x_2003_) as u8);
    if v___x_2004_ == 0 {
        let mut v___x_2005_: u8 = 0;
        let mut v___x_2006_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2007_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_2005_ = 1;
        v___x_2006_ = crate::leanh::lean_box((v___x_2005_) as usize);
        v___x_2007_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_2007_, 0, v_it_2001_);
        crate::leanh::lean_ctor_set(v___x_2007_, 1, v___x_2006_);
        return v___x_2007_;
    } else {
        let mut v___x_2008_: u8 = 0;
        let mut v___x_2009_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2010_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_2008_ = 0;
        v___x_2009_ = crate::leanh::lean_box((v___x_2008_) as usize);
        v___x_2010_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_2010_, 0, v_it_2001_);
        crate::leanh::lean_ctor_set(v___x_2010_, 1, v___x_2009_);
        return v___x_2010_;
    }
}
pub unsafe fn l_Std_Internal_Parsec_isEof___boxed(
    mut v_00_u03b9_2011_: *mut crate::leanh::LeanObject,
    mut v_elem_2012_: *mut crate::leanh::LeanObject,
    mut v_idx_2013_: *mut crate::leanh::LeanObject,
    mut v_inst_2014_: *mut crate::leanh::LeanObject,
    mut v_inst_2015_: *mut crate::leanh::LeanObject,
    mut v_inst_2016_: *mut crate::leanh::LeanObject,
    mut v_it_2017_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2018_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2018_ = l_Std_Internal_Parsec_isEof(
        v_00_u03b9_2011_,
        v_elem_2012_,
        v_idx_2013_,
        v_inst_2014_,
        v_inst_2015_,
        v_inst_2016_,
        v_it_2017_,
    );
    crate::leanh::lean_dec_ref(v_inst_2015_);
    crate::leanh::lean_dec_ref(v_inst_2014_);
    return v_res_2018_;
}
pub unsafe fn l_Std_Internal_Parsec_manyCore___redArg(
    mut v_inst_2019_: *mut crate::leanh::LeanObject,
    mut v_inst_2020_: *mut crate::leanh::LeanObject,
    mut v_p_2021_: *mut crate::leanh::LeanObject,
    mut v_acc_2022_: *mut crate::leanh::LeanObject,
    mut v_a_2023_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2024_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_pos_2025_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_res_2026_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2027_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_pos_2029_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_err_2030_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2032_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2033_: u8 = 0;
    let mut v_pos_2034_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2035_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2036_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2037_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2038_: u8 = 0;
    let mut v___x_2040_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2041_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2043_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2044_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2045_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                crate::leanh::lean_inc_ref(v_p_2021_);
                crate::leanh::lean_inc(v_a_2023_);
                v___x_2024_ = crate::leanh::lean_apply_1(v_p_2021_, v_a_2023_);
                if crate::leanh::lean_obj_tag(v___x_2024_) == 0 {
                    crate::leanh::lean_dec(v_a_2023_);
                    v_pos_2025_ = crate::leanh::lean_ctor_get(v___x_2024_, 0);
                    crate::leanh::lean_inc(v_pos_2025_);
                    v_res_2026_ = crate::leanh::lean_ctor_get(v___x_2024_, 1);
                    crate::leanh::lean_inc(v_res_2026_);
                    crate::leanh::lean_dec_ref_known(v___x_2024_, 2);
                    v___x_2027_ = lean_array_push(v_acc_2022_, v_res_2026_);
                    v_acc_2022_ = v___x_2027_;
                    v_a_2023_ = v_pos_2025_;
                    state = 0;
                    continue;
                } else {
                    crate::leanh::lean_dec_ref(v_p_2021_);
                    v_pos_2029_ = crate::leanh::lean_ctor_get(v___x_2024_, 0);
                    v_err_2030_ = crate::leanh::lean_ctor_get(v___x_2024_, 1);
                    v_isSharedCheck_2045_ = (!crate::leanh::lean_is_exclusive(v___x_2024_)) as u8;
                    if v_isSharedCheck_2045_ == 0 {
                        v___x_2032_ = v___x_2024_;
                        v_isShared_2033_ = v_isSharedCheck_2045_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_err_2030_);
                        crate::leanh::lean_inc(v_pos_2029_);
                        crate::leanh::lean_dec(v___x_2024_);
                        v___x_2032_ = crate::leanh::lean_box(0);
                        v_isShared_2033_ = v_isSharedCheck_2045_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v_pos_2034_ = crate::leanh::lean_ctor_get(v_inst_2020_, 0);
                crate::leanh::lean_inc_n(v_pos_2034_, 2);
                crate::leanh::lean_dec_ref(v_inst_2020_);
                v___x_2035_ = crate::leanh::lean_apply_1(v_pos_2034_, v_a_2023_);
                crate::leanh::lean_inc(v_pos_2029_);
                v___x_2036_ = crate::leanh::lean_apply_1(v_pos_2034_, v_pos_2029_);
                v___x_2037_ = crate::leanh::lean_apply_2(v_inst_2019_, v___x_2035_, v___x_2036_);
                v___x_2038_ = (crate::leanh::lean_unbox(v___x_2037_) as u8);
                if v___x_2038_ == 0 {
                    crate::leanh::lean_dec_ref(v_acc_2022_);
                    if v_isShared_2033_ == 0 {
                        v___x_2040_ = v___x_2032_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_2041_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2041_, 0, v_pos_2029_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2041_, 1, v_err_2030_);
                        v___x_2040_ = v_reuseFailAlloc_2041_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_err_2030_);
                    if v_isShared_2033_ == 0 {
                        crate::leanh::lean_ctor_set_tag(v___x_2032_, 0);
                        crate::leanh::lean_ctor_set(v___x_2032_, 1, v_acc_2022_);
                        v___x_2043_ = v___x_2032_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_2044_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2044_, 0, v_pos_2029_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2044_, 1, v_acc_2022_);
                        v___x_2043_ = v_reuseFailAlloc_2044_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_2040_;
            }
            3 => {
                return v___x_2043_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Internal_Parsec_manyCore(
    mut v_00_u03b1_2046_: *mut crate::leanh::LeanObject,
    mut v_00_u03b9_2047_: *mut crate::leanh::LeanObject,
    mut v_elem_2048_: *mut crate::leanh::LeanObject,
    mut v_idx_2049_: *mut crate::leanh::LeanObject,
    mut v_inst_2050_: *mut crate::leanh::LeanObject,
    mut v_inst_2051_: *mut crate::leanh::LeanObject,
    mut v_inst_2052_: *mut crate::leanh::LeanObject,
    mut v_p_2053_: *mut crate::leanh::LeanObject,
    mut v_acc_2054_: *mut crate::leanh::LeanObject,
    mut v_a_2055_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2056_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2056_ = l_Std_Internal_Parsec_manyCore___redArg(
        v_inst_2050_,
        v_inst_2052_,
        v_p_2053_,
        v_acc_2054_,
        v_a_2055_,
    );
    return v___x_2056_;
}
pub unsafe fn l_Std_Internal_Parsec_manyCore___boxed(
    mut v_00_u03b1_2057_: *mut crate::leanh::LeanObject,
    mut v_00_u03b9_2058_: *mut crate::leanh::LeanObject,
    mut v_elem_2059_: *mut crate::leanh::LeanObject,
    mut v_idx_2060_: *mut crate::leanh::LeanObject,
    mut v_inst_2061_: *mut crate::leanh::LeanObject,
    mut v_inst_2062_: *mut crate::leanh::LeanObject,
    mut v_inst_2063_: *mut crate::leanh::LeanObject,
    mut v_p_2064_: *mut crate::leanh::LeanObject,
    mut v_acc_2065_: *mut crate::leanh::LeanObject,
    mut v_a_2066_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2067_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2067_ = l_Std_Internal_Parsec_manyCore(
        v_00_u03b1_2057_,
        v_00_u03b9_2058_,
        v_elem_2059_,
        v_idx_2060_,
        v_inst_2061_,
        v_inst_2062_,
        v_inst_2063_,
        v_p_2064_,
        v_acc_2065_,
        v_a_2066_,
    );
    crate::leanh::lean_dec_ref(v_inst_2062_);
    return v_res_2067_;
}
pub unsafe fn l_Std_Internal_Parsec_many___redArg(
    mut v_inst_2070_: *mut crate::leanh::LeanObject,
    mut v_inst_2071_: *mut crate::leanh::LeanObject,
    mut v_p_2072_: *mut crate::leanh::LeanObject,
    mut v_a_2073_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2074_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2075_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2074_ = l_Std_Internal_Parsec_many___redArg___closed__0;
    v___x_2075_ = l_Std_Internal_Parsec_manyCore___redArg(
        v_inst_2070_,
        v_inst_2071_,
        v_p_2072_,
        v___x_2074_,
        v_a_2073_,
    );
    return v___x_2075_;
}
pub unsafe fn l_Std_Internal_Parsec_many(
    mut v_00_u03b1_2076_: *mut crate::leanh::LeanObject,
    mut v_00_u03b9_2077_: *mut crate::leanh::LeanObject,
    mut v_elem_2078_: *mut crate::leanh::LeanObject,
    mut v_idx_2079_: *mut crate::leanh::LeanObject,
    mut v_inst_2080_: *mut crate::leanh::LeanObject,
    mut v_inst_2081_: *mut crate::leanh::LeanObject,
    mut v_inst_2082_: *mut crate::leanh::LeanObject,
    mut v_p_2083_: *mut crate::leanh::LeanObject,
    mut v_a_2084_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2085_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2086_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2085_ = l_Std_Internal_Parsec_many___redArg___closed__0;
    v___x_2086_ = l_Std_Internal_Parsec_manyCore___redArg(
        v_inst_2080_,
        v_inst_2082_,
        v_p_2083_,
        v___x_2085_,
        v_a_2084_,
    );
    return v___x_2086_;
}
pub unsafe fn l_Std_Internal_Parsec_many___boxed(
    mut v_00_u03b1_2087_: *mut crate::leanh::LeanObject,
    mut v_00_u03b9_2088_: *mut crate::leanh::LeanObject,
    mut v_elem_2089_: *mut crate::leanh::LeanObject,
    mut v_idx_2090_: *mut crate::leanh::LeanObject,
    mut v_inst_2091_: *mut crate::leanh::LeanObject,
    mut v_inst_2092_: *mut crate::leanh::LeanObject,
    mut v_inst_2093_: *mut crate::leanh::LeanObject,
    mut v_p_2094_: *mut crate::leanh::LeanObject,
    mut v_a_2095_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2096_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2096_ = l_Std_Internal_Parsec_many(
        v_00_u03b1_2087_,
        v_00_u03b9_2088_,
        v_elem_2089_,
        v_idx_2090_,
        v_inst_2091_,
        v_inst_2092_,
        v_inst_2093_,
        v_p_2094_,
        v_a_2095_,
    );
    crate::leanh::lean_dec_ref(v_inst_2092_);
    return v_res_2096_;
}
pub unsafe fn l_Std_Internal_Parsec_many1___redArg(
    mut v_inst_2097_: *mut crate::leanh::LeanObject,
    mut v_inst_2098_: *mut crate::leanh::LeanObject,
    mut v_p_2099_: *mut crate::leanh::LeanObject,
    mut v_a_2100_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2101_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_pos_2102_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_res_2103_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2104_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2105_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2106_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2107_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_pos_2108_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_err_2109_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2111_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2112_: u8 = 0;
    let mut v___x_2114_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2115_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2116_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                crate::leanh::lean_inc_ref(v_p_2099_);
                v___x_2101_ = crate::leanh::lean_apply_1(v_p_2099_, v_a_2100_);
                if crate::leanh::lean_obj_tag(v___x_2101_) == 0 {
                    v_pos_2102_ = crate::leanh::lean_ctor_get(v___x_2101_, 0);
                    crate::leanh::lean_inc(v_pos_2102_);
                    v_res_2103_ = crate::leanh::lean_ctor_get(v___x_2101_, 1);
                    crate::leanh::lean_inc(v_res_2103_);
                    crate::leanh::lean_dec_ref_known(v___x_2101_, 2);
                    v___x_2104_ = crate::leanh::lean_unsigned_to_nat(1);
                    v___x_2105_ = lean_mk_empty_array_with_capacity(v___x_2104_);
                    v___x_2106_ = lean_array_push(v___x_2105_, v_res_2103_);
                    v___x_2107_ = l_Std_Internal_Parsec_manyCore___redArg(
                        v_inst_2097_,
                        v_inst_2098_,
                        v_p_2099_,
                        v___x_2106_,
                        v_pos_2102_,
                    );
                    return v___x_2107_;
                } else {
                    crate::leanh::lean_dec_ref(v_p_2099_);
                    crate::leanh::lean_dec_ref(v_inst_2098_);
                    crate::leanh::lean_dec_ref(v_inst_2097_);
                    v_pos_2108_ = crate::leanh::lean_ctor_get(v___x_2101_, 0);
                    v_err_2109_ = crate::leanh::lean_ctor_get(v___x_2101_, 1);
                    v_isSharedCheck_2116_ = (!crate::leanh::lean_is_exclusive(v___x_2101_)) as u8;
                    if v_isSharedCheck_2116_ == 0 {
                        v___x_2111_ = v___x_2101_;
                        v_isShared_2112_ = v_isSharedCheck_2116_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_err_2109_);
                        crate::leanh::lean_inc(v_pos_2108_);
                        crate::leanh::lean_dec(v___x_2101_);
                        v___x_2111_ = crate::leanh::lean_box(0);
                        v_isShared_2112_ = v_isSharedCheck_2116_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_2112_ == 0 {
                    v___x_2114_ = v___x_2111_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2115_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2115_, 0, v_pos_2108_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2115_, 1, v_err_2109_);
                    v___x_2114_ = v_reuseFailAlloc_2115_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_2114_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Internal_Parsec_many1(
    mut v_00_u03b1_2117_: *mut crate::leanh::LeanObject,
    mut v_00_u03b9_2118_: *mut crate::leanh::LeanObject,
    mut v_elem_2119_: *mut crate::leanh::LeanObject,
    mut v_idx_2120_: *mut crate::leanh::LeanObject,
    mut v_inst_2121_: *mut crate::leanh::LeanObject,
    mut v_inst_2122_: *mut crate::leanh::LeanObject,
    mut v_inst_2123_: *mut crate::leanh::LeanObject,
    mut v_p_2124_: *mut crate::leanh::LeanObject,
    mut v_a_2125_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2126_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_pos_2127_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_res_2128_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2129_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2130_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2131_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2132_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_pos_2133_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_err_2134_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2136_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2137_: u8 = 0;
    let mut v___x_2139_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2140_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2141_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                crate::leanh::lean_inc_ref(v_p_2124_);
                v___x_2126_ = crate::leanh::lean_apply_1(v_p_2124_, v_a_2125_);
                if crate::leanh::lean_obj_tag(v___x_2126_) == 0 {
                    v_pos_2127_ = crate::leanh::lean_ctor_get(v___x_2126_, 0);
                    crate::leanh::lean_inc(v_pos_2127_);
                    v_res_2128_ = crate::leanh::lean_ctor_get(v___x_2126_, 1);
                    crate::leanh::lean_inc(v_res_2128_);
                    crate::leanh::lean_dec_ref_known(v___x_2126_, 2);
                    v___x_2129_ = crate::leanh::lean_unsigned_to_nat(1);
                    v___x_2130_ = lean_mk_empty_array_with_capacity(v___x_2129_);
                    v___x_2131_ = lean_array_push(v___x_2130_, v_res_2128_);
                    v___x_2132_ = l_Std_Internal_Parsec_manyCore___redArg(
                        v_inst_2121_,
                        v_inst_2123_,
                        v_p_2124_,
                        v___x_2131_,
                        v_pos_2127_,
                    );
                    return v___x_2132_;
                } else {
                    crate::leanh::lean_dec_ref(v_p_2124_);
                    crate::leanh::lean_dec_ref(v_inst_2123_);
                    crate::leanh::lean_dec_ref(v_inst_2121_);
                    v_pos_2133_ = crate::leanh::lean_ctor_get(v___x_2126_, 0);
                    v_err_2134_ = crate::leanh::lean_ctor_get(v___x_2126_, 1);
                    v_isSharedCheck_2141_ = (!crate::leanh::lean_is_exclusive(v___x_2126_)) as u8;
                    if v_isSharedCheck_2141_ == 0 {
                        v___x_2136_ = v___x_2126_;
                        v_isShared_2137_ = v_isSharedCheck_2141_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_err_2134_);
                        crate::leanh::lean_inc(v_pos_2133_);
                        crate::leanh::lean_dec(v___x_2126_);
                        v___x_2136_ = crate::leanh::lean_box(0);
                        v_isShared_2137_ = v_isSharedCheck_2141_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_2137_ == 0 {
                    v___x_2139_ = v___x_2136_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2140_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2140_, 0, v_pos_2133_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2140_, 1, v_err_2134_);
                    v___x_2139_ = v_reuseFailAlloc_2140_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_2139_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Internal_Parsec_many1___boxed(
    mut v_00_u03b1_2142_: *mut crate::leanh::LeanObject,
    mut v_00_u03b9_2143_: *mut crate::leanh::LeanObject,
    mut v_elem_2144_: *mut crate::leanh::LeanObject,
    mut v_idx_2145_: *mut crate::leanh::LeanObject,
    mut v_inst_2146_: *mut crate::leanh::LeanObject,
    mut v_inst_2147_: *mut crate::leanh::LeanObject,
    mut v_inst_2148_: *mut crate::leanh::LeanObject,
    mut v_p_2149_: *mut crate::leanh::LeanObject,
    mut v_a_2150_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2151_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2151_ = l_Std_Internal_Parsec_many1(
        v_00_u03b1_2142_,
        v_00_u03b9_2143_,
        v_elem_2144_,
        v_idx_2145_,
        v_inst_2146_,
        v_inst_2147_,
        v_inst_2148_,
        v_p_2149_,
        v_a_2150_,
    );
    crate::leanh::lean_dec_ref(v_inst_2147_);
    return v_res_2151_;
}
pub unsafe fn l_Std_Internal_Parsec_any___redArg(
    mut v_inst_2152_: *mut crate::leanh::LeanObject,
    mut v_it_2153_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_hasNext_2154_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_next_x27_2155_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_curr_x27_2156_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2157_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2158_: u8 = 0;
    v_hasNext_2154_ = crate::leanh::lean_ctor_get(v_inst_2152_, 3);
    crate::leanh::lean_inc_ref(v_hasNext_2154_);
    v_next_x27_2155_ = crate::leanh::lean_ctor_get(v_inst_2152_, 4);
    crate::leanh::lean_inc(v_next_x27_2155_);
    v_curr_x27_2156_ = crate::leanh::lean_ctor_get(v_inst_2152_, 5);
    crate::leanh::lean_inc(v_curr_x27_2156_);
    crate::leanh::lean_dec_ref(v_inst_2152_);
    crate::leanh::lean_inc(v_it_2153_);
    v___x_2157_ = crate::leanh::lean_apply_1(v_hasNext_2154_, v_it_2153_);
    v___x_2158_ = (crate::leanh::lean_unbox(v___x_2157_) as u8);
    if v___x_2158_ == 0 {
        let mut v___x_2159_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2160_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_curr_x27_2156_);
        crate::leanh::lean_dec(v_next_x27_2155_);
        v___x_2159_ = crate::leanh::lean_box(0);
        v___x_2160_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_2160_, 0, v_it_2153_);
        crate::leanh::lean_ctor_set(v___x_2160_, 1, v___x_2159_);
        return v___x_2160_;
    } else {
        let mut v_c_2161_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_it_x27_2162_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2163_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_inc(v_it_2153_);
        v_c_2161_ =
            crate::leanh::lean_apply_2(v_curr_x27_2156_, v_it_2153_, crate::leanh::lean_box(0));
        v_it_x27_2162_ =
            crate::leanh::lean_apply_2(v_next_x27_2155_, v_it_2153_, crate::leanh::lean_box(0));
        v___x_2163_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_2163_, 0, v_it_x27_2162_);
        crate::leanh::lean_ctor_set(v___x_2163_, 1, v_c_2161_);
        return v___x_2163_;
    }
}
pub unsafe fn l_Std_Internal_Parsec_any(
    mut v_00_u03b9_2164_: *mut crate::leanh::LeanObject,
    mut v_elem_2165_: *mut crate::leanh::LeanObject,
    mut v_idx_2166_: *mut crate::leanh::LeanObject,
    mut v_inst_2167_: *mut crate::leanh::LeanObject,
    mut v_inst_2168_: *mut crate::leanh::LeanObject,
    mut v_inst_2169_: *mut crate::leanh::LeanObject,
    mut v_it_2170_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_hasNext_2171_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_next_x27_2172_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_curr_x27_2173_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2174_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2175_: u8 = 0;
    v_hasNext_2171_ = crate::leanh::lean_ctor_get(v_inst_2169_, 3);
    crate::leanh::lean_inc_ref(v_hasNext_2171_);
    v_next_x27_2172_ = crate::leanh::lean_ctor_get(v_inst_2169_, 4);
    crate::leanh::lean_inc(v_next_x27_2172_);
    v_curr_x27_2173_ = crate::leanh::lean_ctor_get(v_inst_2169_, 5);
    crate::leanh::lean_inc(v_curr_x27_2173_);
    crate::leanh::lean_dec_ref(v_inst_2169_);
    crate::leanh::lean_inc(v_it_2170_);
    v___x_2174_ = crate::leanh::lean_apply_1(v_hasNext_2171_, v_it_2170_);
    v___x_2175_ = (crate::leanh::lean_unbox(v___x_2174_) as u8);
    if v___x_2175_ == 0 {
        let mut v___x_2176_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2177_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_curr_x27_2173_);
        crate::leanh::lean_dec(v_next_x27_2172_);
        v___x_2176_ = crate::leanh::lean_box(0);
        v___x_2177_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_2177_, 0, v_it_2170_);
        crate::leanh::lean_ctor_set(v___x_2177_, 1, v___x_2176_);
        return v___x_2177_;
    } else {
        let mut v_c_2178_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_it_x27_2179_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2180_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_inc(v_it_2170_);
        v_c_2178_ =
            crate::leanh::lean_apply_2(v_curr_x27_2173_, v_it_2170_, crate::leanh::lean_box(0));
        v_it_x27_2179_ =
            crate::leanh::lean_apply_2(v_next_x27_2172_, v_it_2170_, crate::leanh::lean_box(0));
        v___x_2180_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_2180_, 0, v_it_x27_2179_);
        crate::leanh::lean_ctor_set(v___x_2180_, 1, v_c_2178_);
        return v___x_2180_;
    }
}
pub unsafe fn l_Std_Internal_Parsec_any___boxed(
    mut v_00_u03b9_2181_: *mut crate::leanh::LeanObject,
    mut v_elem_2182_: *mut crate::leanh::LeanObject,
    mut v_idx_2183_: *mut crate::leanh::LeanObject,
    mut v_inst_2184_: *mut crate::leanh::LeanObject,
    mut v_inst_2185_: *mut crate::leanh::LeanObject,
    mut v_inst_2186_: *mut crate::leanh::LeanObject,
    mut v_it_2187_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2188_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2188_ = l_Std_Internal_Parsec_any(
        v_00_u03b9_2181_,
        v_elem_2182_,
        v_idx_2183_,
        v_inst_2184_,
        v_inst_2185_,
        v_inst_2186_,
        v_it_2187_,
    );
    crate::leanh::lean_dec_ref(v_inst_2185_);
    crate::leanh::lean_dec_ref(v_inst_2184_);
    return v_res_2188_;
}
pub unsafe fn l_Std_Internal_Parsec_satisfy___redArg(
    mut v_inst_2192_: *mut crate::leanh::LeanObject,
    mut v_p_2193_: *mut crate::leanh::LeanObject,
    mut v_a_2194_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_hasNext_2195_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_next_x27_2196_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_curr_x27_2197_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2198_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2199_: u8 = 0;
    v_hasNext_2195_ = crate::leanh::lean_ctor_get(v_inst_2192_, 3);
    crate::leanh::lean_inc_ref(v_hasNext_2195_);
    v_next_x27_2196_ = crate::leanh::lean_ctor_get(v_inst_2192_, 4);
    crate::leanh::lean_inc(v_next_x27_2196_);
    v_curr_x27_2197_ = crate::leanh::lean_ctor_get(v_inst_2192_, 5);
    crate::leanh::lean_inc(v_curr_x27_2197_);
    crate::leanh::lean_dec_ref(v_inst_2192_);
    crate::leanh::lean_inc(v_a_2194_);
    v___x_2198_ = crate::leanh::lean_apply_1(v_hasNext_2195_, v_a_2194_);
    v___x_2199_ = (crate::leanh::lean_unbox(v___x_2198_) as u8);
    if v___x_2199_ == 0 {
        let mut v___x_2200_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2201_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_curr_x27_2197_);
        crate::leanh::lean_dec(v_next_x27_2196_);
        crate::leanh::lean_dec_ref(v_p_2193_);
        v___x_2200_ = crate::leanh::lean_box(0);
        v___x_2201_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_2201_, 0, v_a_2194_);
        crate::leanh::lean_ctor_set(v___x_2201_, 1, v___x_2200_);
        return v___x_2201_;
    } else {
        let mut v_c_2202_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_it_x27_2203_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2204_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2205_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2206_: u8 = 0;
        crate::leanh::lean_inc_n(v_a_2194_, 2);
        v_c_2202_ =
            crate::leanh::lean_apply_2(v_curr_x27_2197_, v_a_2194_, crate::leanh::lean_box(0));
        v_it_x27_2203_ =
            crate::leanh::lean_apply_2(v_next_x27_2196_, v_a_2194_, crate::leanh::lean_box(0));
        crate::leanh::lean_inc(v_c_2202_);
        v___x_2204_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_2204_, 0, v_it_x27_2203_);
        crate::leanh::lean_ctor_set(v___x_2204_, 1, v_c_2202_);
        v___x_2205_ = crate::leanh::lean_apply_1(v_p_2193_, v_c_2202_);
        v___x_2206_ = (crate::leanh::lean_unbox(v___x_2205_) as u8);
        if v___x_2206_ == 0 {
            let mut v___x_2207_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_2208_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec_ref_known(v___x_2204_, 2);
            v___x_2207_ = l_Std_Internal_Parsec_satisfy___redArg___closed__1;
            v___x_2208_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
            crate::leanh::lean_ctor_set(v___x_2208_, 0, v_a_2194_);
            crate::leanh::lean_ctor_set(v___x_2208_, 1, v___x_2207_);
            return v___x_2208_;
        } else {
            crate::leanh::lean_dec(v_a_2194_);
            return v___x_2204_;
        }
    }
}
pub unsafe fn l_Std_Internal_Parsec_satisfy(
    mut v_00_u03b9_2209_: *mut crate::leanh::LeanObject,
    mut v_elem_2210_: *mut crate::leanh::LeanObject,
    mut v_idx_2211_: *mut crate::leanh::LeanObject,
    mut v_inst_2212_: *mut crate::leanh::LeanObject,
    mut v_inst_2213_: *mut crate::leanh::LeanObject,
    mut v_inst_2214_: *mut crate::leanh::LeanObject,
    mut v_p_2215_: *mut crate::leanh::LeanObject,
    mut v_a_2216_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_hasNext_2217_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_next_x27_2218_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_curr_x27_2219_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2220_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2221_: u8 = 0;
    v_hasNext_2217_ = crate::leanh::lean_ctor_get(v_inst_2214_, 3);
    crate::leanh::lean_inc_ref(v_hasNext_2217_);
    v_next_x27_2218_ = crate::leanh::lean_ctor_get(v_inst_2214_, 4);
    crate::leanh::lean_inc(v_next_x27_2218_);
    v_curr_x27_2219_ = crate::leanh::lean_ctor_get(v_inst_2214_, 5);
    crate::leanh::lean_inc(v_curr_x27_2219_);
    crate::leanh::lean_dec_ref(v_inst_2214_);
    crate::leanh::lean_inc(v_a_2216_);
    v___x_2220_ = crate::leanh::lean_apply_1(v_hasNext_2217_, v_a_2216_);
    v___x_2221_ = (crate::leanh::lean_unbox(v___x_2220_) as u8);
    if v___x_2221_ == 0 {
        let mut v___x_2222_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2223_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_curr_x27_2219_);
        crate::leanh::lean_dec(v_next_x27_2218_);
        crate::leanh::lean_dec_ref(v_p_2215_);
        v___x_2222_ = crate::leanh::lean_box(0);
        v___x_2223_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_2223_, 0, v_a_2216_);
        crate::leanh::lean_ctor_set(v___x_2223_, 1, v___x_2222_);
        return v___x_2223_;
    } else {
        let mut v_c_2224_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_it_x27_2225_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2226_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2227_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2228_: u8 = 0;
        crate::leanh::lean_inc_n(v_a_2216_, 2);
        v_c_2224_ =
            crate::leanh::lean_apply_2(v_curr_x27_2219_, v_a_2216_, crate::leanh::lean_box(0));
        v_it_x27_2225_ =
            crate::leanh::lean_apply_2(v_next_x27_2218_, v_a_2216_, crate::leanh::lean_box(0));
        crate::leanh::lean_inc(v_c_2224_);
        v___x_2226_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_2226_, 0, v_it_x27_2225_);
        crate::leanh::lean_ctor_set(v___x_2226_, 1, v_c_2224_);
        v___x_2227_ = crate::leanh::lean_apply_1(v_p_2215_, v_c_2224_);
        v___x_2228_ = (crate::leanh::lean_unbox(v___x_2227_) as u8);
        if v___x_2228_ == 0 {
            let mut v___x_2229_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_2230_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec_ref_known(v___x_2226_, 2);
            v___x_2229_ = l_Std_Internal_Parsec_satisfy___redArg___closed__1;
            v___x_2230_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
            crate::leanh::lean_ctor_set(v___x_2230_, 0, v_a_2216_);
            crate::leanh::lean_ctor_set(v___x_2230_, 1, v___x_2229_);
            return v___x_2230_;
        } else {
            crate::leanh::lean_dec(v_a_2216_);
            return v___x_2226_;
        }
    }
}
pub unsafe fn l_Std_Internal_Parsec_satisfy___boxed(
    mut v_00_u03b9_2231_: *mut crate::leanh::LeanObject,
    mut v_elem_2232_: *mut crate::leanh::LeanObject,
    mut v_idx_2233_: *mut crate::leanh::LeanObject,
    mut v_inst_2234_: *mut crate::leanh::LeanObject,
    mut v_inst_2235_: *mut crate::leanh::LeanObject,
    mut v_inst_2236_: *mut crate::leanh::LeanObject,
    mut v_p_2237_: *mut crate::leanh::LeanObject,
    mut v_a_2238_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2239_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2239_ = l_Std_Internal_Parsec_satisfy(
        v_00_u03b9_2231_,
        v_elem_2232_,
        v_idx_2233_,
        v_inst_2234_,
        v_inst_2235_,
        v_inst_2236_,
        v_p_2237_,
        v_a_2238_,
    );
    crate::leanh::lean_dec_ref(v_inst_2235_);
    crate::leanh::lean_dec_ref(v_inst_2234_);
    return v_res_2239_;
}
pub unsafe fn l_Std_Internal_Parsec_notFollowedBy___redArg(
    mut v_p_2240_: *mut crate::leanh::LeanObject,
    mut v_it_2241_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2242_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2244_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2245_: u8 = 0;
    let mut v___x_2246_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2248_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2249_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2250_: u8 = 0;
    let mut v_unused_2251_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2252_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2254_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2255_: u8 = 0;
    let mut v___x_2256_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2258_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2259_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2260_: u8 = 0;
    let mut v_unused_2261_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2262_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                crate::leanh::lean_inc(v_it_2241_);
                v___x_2242_ = crate::leanh::lean_apply_1(v_p_2240_, v_it_2241_);
                if crate::leanh::lean_obj_tag(v___x_2242_) == 0 {
                    v_isSharedCheck_2250_ = (!crate::leanh::lean_is_exclusive(v___x_2242_)) as u8;
                    if v_isSharedCheck_2250_ == 0 {
                        v_unused_2251_ = crate::leanh::lean_ctor_get(v___x_2242_, 1);
                        crate::leanh::lean_dec(v_unused_2251_);
                        v_unused_2252_ = crate::leanh::lean_ctor_get(v___x_2242_, 0);
                        crate::leanh::lean_dec(v_unused_2252_);
                        v___x_2244_ = v___x_2242_;
                        v_isShared_2245_ = v_isSharedCheck_2250_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v___x_2242_);
                        v___x_2244_ = crate::leanh::lean_box(0);
                        v_isShared_2245_ = v_isSharedCheck_2250_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_isSharedCheck_2260_ = (!crate::leanh::lean_is_exclusive(v___x_2242_)) as u8;
                    if v_isSharedCheck_2260_ == 0 {
                        v_unused_2261_ = crate::leanh::lean_ctor_get(v___x_2242_, 1);
                        crate::leanh::lean_dec(v_unused_2261_);
                        v_unused_2262_ = crate::leanh::lean_ctor_get(v___x_2242_, 0);
                        crate::leanh::lean_dec(v_unused_2262_);
                        v___x_2254_ = v___x_2242_;
                        v_isShared_2255_ = v_isSharedCheck_2260_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v___x_2242_);
                        v___x_2254_ = crate::leanh::lean_box(0);
                        v_isShared_2255_ = v_isSharedCheck_2260_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v___x_2246_ = l_Std_Internal_Parsec_instInhabited___lam__0___closed__1;
                if v_isShared_2245_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_2244_, 1);
                    crate::leanh::lean_ctor_set(v___x_2244_, 1, v___x_2246_);
                    crate::leanh::lean_ctor_set(v___x_2244_, 0, v_it_2241_);
                    v___x_2248_ = v___x_2244_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2249_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2249_, 0, v_it_2241_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2249_, 1, v___x_2246_);
                    v___x_2248_ = v_reuseFailAlloc_2249_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_2248_;
            }
            3 => {
                v___x_2256_ = crate::leanh::lean_box(0);
                if v_isShared_2255_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_2254_, 0);
                    crate::leanh::lean_ctor_set(v___x_2254_, 1, v___x_2256_);
                    crate::leanh::lean_ctor_set(v___x_2254_, 0, v_it_2241_);
                    v___x_2258_ = v___x_2254_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2259_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2259_, 0, v_it_2241_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2259_, 1, v___x_2256_);
                    v___x_2258_ = v_reuseFailAlloc_2259_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_2258_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Internal_Parsec_notFollowedBy(
    mut v_00_u03b1_2263_: *mut crate::leanh::LeanObject,
    mut v_00_u03b9_2264_: *mut crate::leanh::LeanObject,
    mut v_p_2265_: *mut crate::leanh::LeanObject,
    mut v_it_2266_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2267_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2269_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2270_: u8 = 0;
    let mut v___x_2271_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2273_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2274_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2275_: u8 = 0;
    let mut v_unused_2276_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2277_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2279_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2280_: u8 = 0;
    let mut v___x_2281_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2283_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2284_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2285_: u8 = 0;
    let mut v_unused_2286_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2287_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                crate::leanh::lean_inc(v_it_2266_);
                v___x_2267_ = crate::leanh::lean_apply_1(v_p_2265_, v_it_2266_);
                if crate::leanh::lean_obj_tag(v___x_2267_) == 0 {
                    v_isSharedCheck_2275_ = (!crate::leanh::lean_is_exclusive(v___x_2267_)) as u8;
                    if v_isSharedCheck_2275_ == 0 {
                        v_unused_2276_ = crate::leanh::lean_ctor_get(v___x_2267_, 1);
                        crate::leanh::lean_dec(v_unused_2276_);
                        v_unused_2277_ = crate::leanh::lean_ctor_get(v___x_2267_, 0);
                        crate::leanh::lean_dec(v_unused_2277_);
                        v___x_2269_ = v___x_2267_;
                        v_isShared_2270_ = v_isSharedCheck_2275_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v___x_2267_);
                        v___x_2269_ = crate::leanh::lean_box(0);
                        v_isShared_2270_ = v_isSharedCheck_2275_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_isSharedCheck_2285_ = (!crate::leanh::lean_is_exclusive(v___x_2267_)) as u8;
                    if v_isSharedCheck_2285_ == 0 {
                        v_unused_2286_ = crate::leanh::lean_ctor_get(v___x_2267_, 1);
                        crate::leanh::lean_dec(v_unused_2286_);
                        v_unused_2287_ = crate::leanh::lean_ctor_get(v___x_2267_, 0);
                        crate::leanh::lean_dec(v_unused_2287_);
                        v___x_2279_ = v___x_2267_;
                        v_isShared_2280_ = v_isSharedCheck_2285_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v___x_2267_);
                        v___x_2279_ = crate::leanh::lean_box(0);
                        v_isShared_2280_ = v_isSharedCheck_2285_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v___x_2271_ = l_Std_Internal_Parsec_instInhabited___lam__0___closed__1;
                if v_isShared_2270_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_2269_, 1);
                    crate::leanh::lean_ctor_set(v___x_2269_, 1, v___x_2271_);
                    crate::leanh::lean_ctor_set(v___x_2269_, 0, v_it_2266_);
                    v___x_2273_ = v___x_2269_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2274_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2274_, 0, v_it_2266_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2274_, 1, v___x_2271_);
                    v___x_2273_ = v_reuseFailAlloc_2274_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_2273_;
            }
            3 => {
                v___x_2281_ = crate::leanh::lean_box(0);
                if v_isShared_2280_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_2279_, 0);
                    crate::leanh::lean_ctor_set(v___x_2279_, 1, v___x_2281_);
                    crate::leanh::lean_ctor_set(v___x_2279_, 0, v_it_2266_);
                    v___x_2283_ = v___x_2279_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2284_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2284_, 0, v_it_2266_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2284_, 1, v___x_2281_);
                    v___x_2283_ = v_reuseFailAlloc_2284_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_2283_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Internal_Parsec_peek_x3f___redArg(
    mut v_inst_2288_: *mut crate::leanh::LeanObject,
    mut v_it_2289_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_hasNext_2290_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_curr_x27_2291_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2292_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2293_: u8 = 0;
    v_hasNext_2290_ = crate::leanh::lean_ctor_get(v_inst_2288_, 3);
    crate::leanh::lean_inc_ref(v_hasNext_2290_);
    v_curr_x27_2291_ = crate::leanh::lean_ctor_get(v_inst_2288_, 5);
    crate::leanh::lean_inc(v_curr_x27_2291_);
    crate::leanh::lean_dec_ref(v_inst_2288_);
    crate::leanh::lean_inc(v_it_2289_);
    v___x_2292_ = crate::leanh::lean_apply_1(v_hasNext_2290_, v_it_2289_);
    v___x_2293_ = (crate::leanh::lean_unbox(v___x_2292_) as u8);
    if v___x_2293_ == 0 {
        let mut v___x_2294_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2295_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_curr_x27_2291_);
        v___x_2294_ = crate::leanh::lean_box(0);
        v___x_2295_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_2295_, 0, v_it_2289_);
        crate::leanh::lean_ctor_set(v___x_2295_, 1, v___x_2294_);
        return v___x_2295_;
    } else {
        let mut v___x_2296_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2297_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2298_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_inc(v_it_2289_);
        v___x_2296_ =
            crate::leanh::lean_apply_2(v_curr_x27_2291_, v_it_2289_, crate::leanh::lean_box(0));
        v___x_2297_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_2297_, 0, v___x_2296_);
        v___x_2298_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_2298_, 0, v_it_2289_);
        crate::leanh::lean_ctor_set(v___x_2298_, 1, v___x_2297_);
        return v___x_2298_;
    }
}
pub unsafe fn l_Std_Internal_Parsec_peek_x3f(
    mut v_00_u03b9_2299_: *mut crate::leanh::LeanObject,
    mut v_elem_2300_: *mut crate::leanh::LeanObject,
    mut v_idx_2301_: *mut crate::leanh::LeanObject,
    mut v_inst_2302_: *mut crate::leanh::LeanObject,
    mut v_inst_2303_: *mut crate::leanh::LeanObject,
    mut v_inst_2304_: *mut crate::leanh::LeanObject,
    mut v_it_2305_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_hasNext_2306_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_curr_x27_2307_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2308_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2309_: u8 = 0;
    v_hasNext_2306_ = crate::leanh::lean_ctor_get(v_inst_2304_, 3);
    crate::leanh::lean_inc_ref(v_hasNext_2306_);
    v_curr_x27_2307_ = crate::leanh::lean_ctor_get(v_inst_2304_, 5);
    crate::leanh::lean_inc(v_curr_x27_2307_);
    crate::leanh::lean_dec_ref(v_inst_2304_);
    crate::leanh::lean_inc(v_it_2305_);
    v___x_2308_ = crate::leanh::lean_apply_1(v_hasNext_2306_, v_it_2305_);
    v___x_2309_ = (crate::leanh::lean_unbox(v___x_2308_) as u8);
    if v___x_2309_ == 0 {
        let mut v___x_2310_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2311_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_curr_x27_2307_);
        v___x_2310_ = crate::leanh::lean_box(0);
        v___x_2311_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_2311_, 0, v_it_2305_);
        crate::leanh::lean_ctor_set(v___x_2311_, 1, v___x_2310_);
        return v___x_2311_;
    } else {
        let mut v___x_2312_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2313_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2314_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_inc(v_it_2305_);
        v___x_2312_ =
            crate::leanh::lean_apply_2(v_curr_x27_2307_, v_it_2305_, crate::leanh::lean_box(0));
        v___x_2313_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_2313_, 0, v___x_2312_);
        v___x_2314_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_2314_, 0, v_it_2305_);
        crate::leanh::lean_ctor_set(v___x_2314_, 1, v___x_2313_);
        return v___x_2314_;
    }
}
pub unsafe fn l_Std_Internal_Parsec_peek_x3f___boxed(
    mut v_00_u03b9_2315_: *mut crate::leanh::LeanObject,
    mut v_elem_2316_: *mut crate::leanh::LeanObject,
    mut v_idx_2317_: *mut crate::leanh::LeanObject,
    mut v_inst_2318_: *mut crate::leanh::LeanObject,
    mut v_inst_2319_: *mut crate::leanh::LeanObject,
    mut v_inst_2320_: *mut crate::leanh::LeanObject,
    mut v_it_2321_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2322_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2322_ = l_Std_Internal_Parsec_peek_x3f(
        v_00_u03b9_2315_,
        v_elem_2316_,
        v_idx_2317_,
        v_inst_2318_,
        v_inst_2319_,
        v_inst_2320_,
        v_it_2321_,
    );
    crate::leanh::lean_dec_ref(v_inst_2319_);
    crate::leanh::lean_dec_ref(v_inst_2318_);
    return v_res_2322_;
}
pub unsafe fn l_Std_Internal_Parsec_peekWhen_x3f___redArg(
    mut v_inst_2323_: *mut crate::leanh::LeanObject,
    mut v_p_2324_: *mut crate::leanh::LeanObject,
    mut v_a_2325_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_hasNext_2326_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_curr_x27_2327_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2328_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2329_: u8 = 0;
    v_hasNext_2326_ = crate::leanh::lean_ctor_get(v_inst_2323_, 3);
    crate::leanh::lean_inc_ref(v_hasNext_2326_);
    v_curr_x27_2327_ = crate::leanh::lean_ctor_get(v_inst_2323_, 5);
    crate::leanh::lean_inc(v_curr_x27_2327_);
    crate::leanh::lean_dec_ref(v_inst_2323_);
    crate::leanh::lean_inc(v_a_2325_);
    v___x_2328_ = crate::leanh::lean_apply_1(v_hasNext_2326_, v_a_2325_);
    v___x_2329_ = (crate::leanh::lean_unbox(v___x_2328_) as u8);
    if v___x_2329_ == 0 {
        let mut v___x_2330_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2331_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_curr_x27_2327_);
        crate::leanh::lean_dec_ref(v_p_2324_);
        v___x_2330_ = crate::leanh::lean_box(0);
        v___x_2331_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_2331_, 0, v_a_2325_);
        crate::leanh::lean_ctor_set(v___x_2331_, 1, v___x_2330_);
        return v___x_2331_;
    } else {
        let mut v___x_2332_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2333_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2334_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2335_: u8 = 0;
        crate::leanh::lean_inc(v_a_2325_);
        v___x_2332_ =
            crate::leanh::lean_apply_2(v_curr_x27_2327_, v_a_2325_, crate::leanh::lean_box(0));
        crate::leanh::lean_inc(v___x_2332_);
        v___x_2333_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_2333_, 0, v___x_2332_);
        v___x_2334_ = crate::leanh::lean_apply_1(v_p_2324_, v___x_2332_);
        v___x_2335_ = (crate::leanh::lean_unbox(v___x_2334_) as u8);
        if v___x_2335_ == 0 {
            let mut v___x_2336_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_2337_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec_ref_known(v___x_2333_, 1);
            v___x_2336_ = crate::leanh::lean_box(0);
            v___x_2337_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
            crate::leanh::lean_ctor_set(v___x_2337_, 0, v_a_2325_);
            crate::leanh::lean_ctor_set(v___x_2337_, 1, v___x_2336_);
            return v___x_2337_;
        } else {
            let mut v___x_2338_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_2338_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
            crate::leanh::lean_ctor_set(v___x_2338_, 0, v_a_2325_);
            crate::leanh::lean_ctor_set(v___x_2338_, 1, v___x_2333_);
            return v___x_2338_;
        }
    }
}
pub unsafe fn l_Std_Internal_Parsec_peekWhen_x3f(
    mut v_00_u03b9_2339_: *mut crate::leanh::LeanObject,
    mut v_elem_2340_: *mut crate::leanh::LeanObject,
    mut v_idx_2341_: *mut crate::leanh::LeanObject,
    mut v_inst_2342_: *mut crate::leanh::LeanObject,
    mut v_inst_2343_: *mut crate::leanh::LeanObject,
    mut v_inst_2344_: *mut crate::leanh::LeanObject,
    mut v_p_2345_: *mut crate::leanh::LeanObject,
    mut v_a_2346_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_hasNext_2347_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_curr_x27_2348_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2349_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2350_: u8 = 0;
    v_hasNext_2347_ = crate::leanh::lean_ctor_get(v_inst_2344_, 3);
    crate::leanh::lean_inc_ref(v_hasNext_2347_);
    v_curr_x27_2348_ = crate::leanh::lean_ctor_get(v_inst_2344_, 5);
    crate::leanh::lean_inc(v_curr_x27_2348_);
    crate::leanh::lean_dec_ref(v_inst_2344_);
    crate::leanh::lean_inc(v_a_2346_);
    v___x_2349_ = crate::leanh::lean_apply_1(v_hasNext_2347_, v_a_2346_);
    v___x_2350_ = (crate::leanh::lean_unbox(v___x_2349_) as u8);
    if v___x_2350_ == 0 {
        let mut v___x_2351_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2352_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_curr_x27_2348_);
        crate::leanh::lean_dec_ref(v_p_2345_);
        v___x_2351_ = crate::leanh::lean_box(0);
        v___x_2352_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_2352_, 0, v_a_2346_);
        crate::leanh::lean_ctor_set(v___x_2352_, 1, v___x_2351_);
        return v___x_2352_;
    } else {
        let mut v___x_2353_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2354_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2355_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2356_: u8 = 0;
        crate::leanh::lean_inc(v_a_2346_);
        v___x_2353_ =
            crate::leanh::lean_apply_2(v_curr_x27_2348_, v_a_2346_, crate::leanh::lean_box(0));
        crate::leanh::lean_inc(v___x_2353_);
        v___x_2354_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_2354_, 0, v___x_2353_);
        v___x_2355_ = crate::leanh::lean_apply_1(v_p_2345_, v___x_2353_);
        v___x_2356_ = (crate::leanh::lean_unbox(v___x_2355_) as u8);
        if v___x_2356_ == 0 {
            let mut v___x_2357_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_2358_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec_ref_known(v___x_2354_, 1);
            v___x_2357_ = crate::leanh::lean_box(0);
            v___x_2358_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
            crate::leanh::lean_ctor_set(v___x_2358_, 0, v_a_2346_);
            crate::leanh::lean_ctor_set(v___x_2358_, 1, v___x_2357_);
            return v___x_2358_;
        } else {
            let mut v___x_2359_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_2359_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
            crate::leanh::lean_ctor_set(v___x_2359_, 0, v_a_2346_);
            crate::leanh::lean_ctor_set(v___x_2359_, 1, v___x_2354_);
            return v___x_2359_;
        }
    }
}
pub unsafe fn l_Std_Internal_Parsec_peekWhen_x3f___boxed(
    mut v_00_u03b9_2360_: *mut crate::leanh::LeanObject,
    mut v_elem_2361_: *mut crate::leanh::LeanObject,
    mut v_idx_2362_: *mut crate::leanh::LeanObject,
    mut v_inst_2363_: *mut crate::leanh::LeanObject,
    mut v_inst_2364_: *mut crate::leanh::LeanObject,
    mut v_inst_2365_: *mut crate::leanh::LeanObject,
    mut v_p_2366_: *mut crate::leanh::LeanObject,
    mut v_a_2367_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2368_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2368_ = l_Std_Internal_Parsec_peekWhen_x3f(
        v_00_u03b9_2360_,
        v_elem_2361_,
        v_idx_2362_,
        v_inst_2363_,
        v_inst_2364_,
        v_inst_2365_,
        v_p_2366_,
        v_a_2367_,
    );
    crate::leanh::lean_dec_ref(v_inst_2364_);
    crate::leanh::lean_dec_ref(v_inst_2363_);
    return v_res_2368_;
}
pub unsafe fn l_Std_Internal_Parsec_peek_x21___redArg(
    mut v_inst_2369_: *mut crate::leanh::LeanObject,
    mut v_it_2370_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_hasNext_2371_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_curr_x27_2372_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2373_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2374_: u8 = 0;
    v_hasNext_2371_ = crate::leanh::lean_ctor_get(v_inst_2369_, 3);
    crate::leanh::lean_inc_ref(v_hasNext_2371_);
    v_curr_x27_2372_ = crate::leanh::lean_ctor_get(v_inst_2369_, 5);
    crate::leanh::lean_inc(v_curr_x27_2372_);
    crate::leanh::lean_dec_ref(v_inst_2369_);
    crate::leanh::lean_inc(v_it_2370_);
    v___x_2373_ = crate::leanh::lean_apply_1(v_hasNext_2371_, v_it_2370_);
    v___x_2374_ = (crate::leanh::lean_unbox(v___x_2373_) as u8);
    if v___x_2374_ == 0 {
        let mut v___x_2375_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2376_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_curr_x27_2372_);
        v___x_2375_ = crate::leanh::lean_box(0);
        v___x_2376_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_2376_, 0, v_it_2370_);
        crate::leanh::lean_ctor_set(v___x_2376_, 1, v___x_2375_);
        return v___x_2376_;
    } else {
        let mut v___x_2377_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2378_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_inc(v_it_2370_);
        v___x_2377_ =
            crate::leanh::lean_apply_2(v_curr_x27_2372_, v_it_2370_, crate::leanh::lean_box(0));
        v___x_2378_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_2378_, 0, v_it_2370_);
        crate::leanh::lean_ctor_set(v___x_2378_, 1, v___x_2377_);
        return v___x_2378_;
    }
}
pub unsafe fn l_Std_Internal_Parsec_peek_x21(
    mut v_00_u03b9_2379_: *mut crate::leanh::LeanObject,
    mut v_elem_2380_: *mut crate::leanh::LeanObject,
    mut v_idx_2381_: *mut crate::leanh::LeanObject,
    mut v_inst_2382_: *mut crate::leanh::LeanObject,
    mut v_inst_2383_: *mut crate::leanh::LeanObject,
    mut v_inst_2384_: *mut crate::leanh::LeanObject,
    mut v_it_2385_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_hasNext_2386_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_curr_x27_2387_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2388_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2389_: u8 = 0;
    v_hasNext_2386_ = crate::leanh::lean_ctor_get(v_inst_2384_, 3);
    crate::leanh::lean_inc_ref(v_hasNext_2386_);
    v_curr_x27_2387_ = crate::leanh::lean_ctor_get(v_inst_2384_, 5);
    crate::leanh::lean_inc(v_curr_x27_2387_);
    crate::leanh::lean_dec_ref(v_inst_2384_);
    crate::leanh::lean_inc(v_it_2385_);
    v___x_2388_ = crate::leanh::lean_apply_1(v_hasNext_2386_, v_it_2385_);
    v___x_2389_ = (crate::leanh::lean_unbox(v___x_2388_) as u8);
    if v___x_2389_ == 0 {
        let mut v___x_2390_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2391_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_curr_x27_2387_);
        v___x_2390_ = crate::leanh::lean_box(0);
        v___x_2391_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_2391_, 0, v_it_2385_);
        crate::leanh::lean_ctor_set(v___x_2391_, 1, v___x_2390_);
        return v___x_2391_;
    } else {
        let mut v___x_2392_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2393_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_inc(v_it_2385_);
        v___x_2392_ =
            crate::leanh::lean_apply_2(v_curr_x27_2387_, v_it_2385_, crate::leanh::lean_box(0));
        v___x_2393_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_2393_, 0, v_it_2385_);
        crate::leanh::lean_ctor_set(v___x_2393_, 1, v___x_2392_);
        return v___x_2393_;
    }
}
pub unsafe fn l_Std_Internal_Parsec_peek_x21___boxed(
    mut v_00_u03b9_2394_: *mut crate::leanh::LeanObject,
    mut v_elem_2395_: *mut crate::leanh::LeanObject,
    mut v_idx_2396_: *mut crate::leanh::LeanObject,
    mut v_inst_2397_: *mut crate::leanh::LeanObject,
    mut v_inst_2398_: *mut crate::leanh::LeanObject,
    mut v_inst_2399_: *mut crate::leanh::LeanObject,
    mut v_it_2400_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2401_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2401_ = l_Std_Internal_Parsec_peek_x21(
        v_00_u03b9_2394_,
        v_elem_2395_,
        v_idx_2396_,
        v_inst_2397_,
        v_inst_2398_,
        v_inst_2399_,
        v_it_2400_,
    );
    crate::leanh::lean_dec_ref(v_inst_2398_);
    crate::leanh::lean_dec_ref(v_inst_2397_);
    return v_res_2401_;
}
pub unsafe fn l_Std_Internal_Parsec_peekD___redArg(
    mut v_inst_2402_: *mut crate::leanh::LeanObject,
    mut v_default_2403_: *mut crate::leanh::LeanObject,
    mut v_it_2404_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_hasNext_2405_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_curr_x27_2406_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2407_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2408_: u8 = 0;
    v_hasNext_2405_ = crate::leanh::lean_ctor_get(v_inst_2402_, 3);
    crate::leanh::lean_inc_ref(v_hasNext_2405_);
    v_curr_x27_2406_ = crate::leanh::lean_ctor_get(v_inst_2402_, 5);
    crate::leanh::lean_inc(v_curr_x27_2406_);
    crate::leanh::lean_dec_ref(v_inst_2402_);
    crate::leanh::lean_inc(v_it_2404_);
    v___x_2407_ = crate::leanh::lean_apply_1(v_hasNext_2405_, v_it_2404_);
    v___x_2408_ = (crate::leanh::lean_unbox(v___x_2407_) as u8);
    if v___x_2408_ == 0 {
        let mut v___x_2409_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_curr_x27_2406_);
        v___x_2409_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_2409_, 0, v_it_2404_);
        crate::leanh::lean_ctor_set(v___x_2409_, 1, v_default_2403_);
        return v___x_2409_;
    } else {
        let mut v___x_2410_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2411_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_default_2403_);
        crate::leanh::lean_inc(v_it_2404_);
        v___x_2410_ =
            crate::leanh::lean_apply_2(v_curr_x27_2406_, v_it_2404_, crate::leanh::lean_box(0));
        v___x_2411_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_2411_, 0, v_it_2404_);
        crate::leanh::lean_ctor_set(v___x_2411_, 1, v___x_2410_);
        return v___x_2411_;
    }
}
pub unsafe fn l_Std_Internal_Parsec_peekD(
    mut v_00_u03b9_2412_: *mut crate::leanh::LeanObject,
    mut v_elem_2413_: *mut crate::leanh::LeanObject,
    mut v_idx_2414_: *mut crate::leanh::LeanObject,
    mut v_inst_2415_: *mut crate::leanh::LeanObject,
    mut v_inst_2416_: *mut crate::leanh::LeanObject,
    mut v_inst_2417_: *mut crate::leanh::LeanObject,
    mut v_default_2418_: *mut crate::leanh::LeanObject,
    mut v_it_2419_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_hasNext_2420_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_curr_x27_2421_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2422_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2423_: u8 = 0;
    v_hasNext_2420_ = crate::leanh::lean_ctor_get(v_inst_2417_, 3);
    crate::leanh::lean_inc_ref(v_hasNext_2420_);
    v_curr_x27_2421_ = crate::leanh::lean_ctor_get(v_inst_2417_, 5);
    crate::leanh::lean_inc(v_curr_x27_2421_);
    crate::leanh::lean_dec_ref(v_inst_2417_);
    crate::leanh::lean_inc(v_it_2419_);
    v___x_2422_ = crate::leanh::lean_apply_1(v_hasNext_2420_, v_it_2419_);
    v___x_2423_ = (crate::leanh::lean_unbox(v___x_2422_) as u8);
    if v___x_2423_ == 0 {
        let mut v___x_2424_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_curr_x27_2421_);
        v___x_2424_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_2424_, 0, v_it_2419_);
        crate::leanh::lean_ctor_set(v___x_2424_, 1, v_default_2418_);
        return v___x_2424_;
    } else {
        let mut v___x_2425_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2426_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_default_2418_);
        crate::leanh::lean_inc(v_it_2419_);
        v___x_2425_ =
            crate::leanh::lean_apply_2(v_curr_x27_2421_, v_it_2419_, crate::leanh::lean_box(0));
        v___x_2426_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_2426_, 0, v_it_2419_);
        crate::leanh::lean_ctor_set(v___x_2426_, 1, v___x_2425_);
        return v___x_2426_;
    }
}
pub unsafe fn l_Std_Internal_Parsec_peekD___boxed(
    mut v_00_u03b9_2427_: *mut crate::leanh::LeanObject,
    mut v_elem_2428_: *mut crate::leanh::LeanObject,
    mut v_idx_2429_: *mut crate::leanh::LeanObject,
    mut v_inst_2430_: *mut crate::leanh::LeanObject,
    mut v_inst_2431_: *mut crate::leanh::LeanObject,
    mut v_inst_2432_: *mut crate::leanh::LeanObject,
    mut v_default_2433_: *mut crate::leanh::LeanObject,
    mut v_it_2434_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2435_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2435_ = l_Std_Internal_Parsec_peekD(
        v_00_u03b9_2427_,
        v_elem_2428_,
        v_idx_2429_,
        v_inst_2430_,
        v_inst_2431_,
        v_inst_2432_,
        v_default_2433_,
        v_it_2434_,
    );
    crate::leanh::lean_dec_ref(v_inst_2431_);
    crate::leanh::lean_dec_ref(v_inst_2430_);
    return v_res_2435_;
}
pub unsafe fn l_Std_Internal_Parsec_skip___redArg(
    mut v_inst_2436_: *mut crate::leanh::LeanObject,
    mut v_it_2437_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_hasNext_2438_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_next_x27_2439_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2440_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2441_: u8 = 0;
    v_hasNext_2438_ = crate::leanh::lean_ctor_get(v_inst_2436_, 3);
    crate::leanh::lean_inc_ref(v_hasNext_2438_);
    v_next_x27_2439_ = crate::leanh::lean_ctor_get(v_inst_2436_, 4);
    crate::leanh::lean_inc(v_next_x27_2439_);
    crate::leanh::lean_dec_ref(v_inst_2436_);
    crate::leanh::lean_inc(v_it_2437_);
    v___x_2440_ = crate::leanh::lean_apply_1(v_hasNext_2438_, v_it_2437_);
    v___x_2441_ = (crate::leanh::lean_unbox(v___x_2440_) as u8);
    if v___x_2441_ == 0 {
        let mut v___x_2442_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2443_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_next_x27_2439_);
        v___x_2442_ = crate::leanh::lean_box(0);
        v___x_2443_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_2443_, 0, v_it_2437_);
        crate::leanh::lean_ctor_set(v___x_2443_, 1, v___x_2442_);
        return v___x_2443_;
    } else {
        let mut v___x_2444_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2445_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2446_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_2444_ =
            crate::leanh::lean_apply_2(v_next_x27_2439_, v_it_2437_, crate::leanh::lean_box(0));
        v___x_2445_ = crate::leanh::lean_box(0);
        v___x_2446_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_2446_, 0, v___x_2444_);
        crate::leanh::lean_ctor_set(v___x_2446_, 1, v___x_2445_);
        return v___x_2446_;
    }
}
pub unsafe fn l_Std_Internal_Parsec_skip(
    mut v_00_u03b9_2447_: *mut crate::leanh::LeanObject,
    mut v_elem_2448_: *mut crate::leanh::LeanObject,
    mut v_idx_2449_: *mut crate::leanh::LeanObject,
    mut v_inst_2450_: *mut crate::leanh::LeanObject,
    mut v_inst_2451_: *mut crate::leanh::LeanObject,
    mut v_inst_2452_: *mut crate::leanh::LeanObject,
    mut v_it_2453_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_hasNext_2454_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_next_x27_2455_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2456_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2457_: u8 = 0;
    v_hasNext_2454_ = crate::leanh::lean_ctor_get(v_inst_2452_, 3);
    crate::leanh::lean_inc_ref(v_hasNext_2454_);
    v_next_x27_2455_ = crate::leanh::lean_ctor_get(v_inst_2452_, 4);
    crate::leanh::lean_inc(v_next_x27_2455_);
    crate::leanh::lean_dec_ref(v_inst_2452_);
    crate::leanh::lean_inc(v_it_2453_);
    v___x_2456_ = crate::leanh::lean_apply_1(v_hasNext_2454_, v_it_2453_);
    v___x_2457_ = (crate::leanh::lean_unbox(v___x_2456_) as u8);
    if v___x_2457_ == 0 {
        let mut v___x_2458_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2459_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_next_x27_2455_);
        v___x_2458_ = crate::leanh::lean_box(0);
        v___x_2459_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_2459_, 0, v_it_2453_);
        crate::leanh::lean_ctor_set(v___x_2459_, 1, v___x_2458_);
        return v___x_2459_;
    } else {
        let mut v___x_2460_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2461_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2462_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_2460_ =
            crate::leanh::lean_apply_2(v_next_x27_2455_, v_it_2453_, crate::leanh::lean_box(0));
        v___x_2461_ = crate::leanh::lean_box(0);
        v___x_2462_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_2462_, 0, v___x_2460_);
        crate::leanh::lean_ctor_set(v___x_2462_, 1, v___x_2461_);
        return v___x_2462_;
    }
}
pub unsafe fn l_Std_Internal_Parsec_skip___boxed(
    mut v_00_u03b9_2463_: *mut crate::leanh::LeanObject,
    mut v_elem_2464_: *mut crate::leanh::LeanObject,
    mut v_idx_2465_: *mut crate::leanh::LeanObject,
    mut v_inst_2466_: *mut crate::leanh::LeanObject,
    mut v_inst_2467_: *mut crate::leanh::LeanObject,
    mut v_inst_2468_: *mut crate::leanh::LeanObject,
    mut v_it_2469_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2470_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2470_ = l_Std_Internal_Parsec_skip(
        v_00_u03b9_2463_,
        v_elem_2464_,
        v_idx_2465_,
        v_inst_2466_,
        v_inst_2467_,
        v_inst_2468_,
        v_it_2469_,
    );
    crate::leanh::lean_dec_ref(v_inst_2467_);
    crate::leanh::lean_dec_ref(v_inst_2466_);
    return v_res_2470_;
}
pub unsafe fn l_Std_Internal_Parsec_manyCharsCore___redArg(
    mut v_inst_2471_: *mut crate::leanh::LeanObject,
    mut v_inst_2472_: *mut crate::leanh::LeanObject,
    mut v_p_2473_: *mut crate::leanh::LeanObject,
    mut v_acc_2474_: *mut crate::leanh::LeanObject,
    mut v_a_2475_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2476_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_pos_2477_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_res_2478_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2479_: u32 = 0;
    let mut v___x_2480_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_pos_2482_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_err_2483_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2485_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2486_: u8 = 0;
    let mut v_pos_2487_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2488_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2489_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2490_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2491_: u8 = 0;
    let mut v___x_2493_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2494_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2496_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2497_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2498_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                crate::leanh::lean_inc_ref(v_p_2473_);
                crate::leanh::lean_inc(v_a_2475_);
                v___x_2476_ = crate::leanh::lean_apply_1(v_p_2473_, v_a_2475_);
                if crate::leanh::lean_obj_tag(v___x_2476_) == 0 {
                    crate::leanh::lean_dec(v_a_2475_);
                    v_pos_2477_ = crate::leanh::lean_ctor_get(v___x_2476_, 0);
                    crate::leanh::lean_inc(v_pos_2477_);
                    v_res_2478_ = crate::leanh::lean_ctor_get(v___x_2476_, 1);
                    crate::leanh::lean_inc(v_res_2478_);
                    crate::leanh::lean_dec_ref_known(v___x_2476_, 2);
                    v___x_2479_ = crate::leanh::lean_unbox_uint32(v_res_2478_);
                    crate::leanh::lean_dec(v_res_2478_);
                    v___x_2480_ = lean_string_push(v_acc_2474_, v___x_2479_);
                    v_acc_2474_ = v___x_2480_;
                    v_a_2475_ = v_pos_2477_;
                    state = 0;
                    continue;
                } else {
                    crate::leanh::lean_dec_ref(v_p_2473_);
                    v_pos_2482_ = crate::leanh::lean_ctor_get(v___x_2476_, 0);
                    v_err_2483_ = crate::leanh::lean_ctor_get(v___x_2476_, 1);
                    v_isSharedCheck_2498_ = (!crate::leanh::lean_is_exclusive(v___x_2476_)) as u8;
                    if v_isSharedCheck_2498_ == 0 {
                        v___x_2485_ = v___x_2476_;
                        v_isShared_2486_ = v_isSharedCheck_2498_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_err_2483_);
                        crate::leanh::lean_inc(v_pos_2482_);
                        crate::leanh::lean_dec(v___x_2476_);
                        v___x_2485_ = crate::leanh::lean_box(0);
                        v_isShared_2486_ = v_isSharedCheck_2498_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v_pos_2487_ = crate::leanh::lean_ctor_get(v_inst_2472_, 0);
                crate::leanh::lean_inc_n(v_pos_2487_, 2);
                crate::leanh::lean_dec_ref(v_inst_2472_);
                v___x_2488_ = crate::leanh::lean_apply_1(v_pos_2487_, v_a_2475_);
                crate::leanh::lean_inc(v_pos_2482_);
                v___x_2489_ = crate::leanh::lean_apply_1(v_pos_2487_, v_pos_2482_);
                v___x_2490_ = crate::leanh::lean_apply_2(v_inst_2471_, v___x_2488_, v___x_2489_);
                v___x_2491_ = (crate::leanh::lean_unbox(v___x_2490_) as u8);
                if v___x_2491_ == 0 {
                    crate::leanh::lean_dec_ref(v_acc_2474_);
                    if v_isShared_2486_ == 0 {
                        v___x_2493_ = v___x_2485_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_2494_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2494_, 0, v_pos_2482_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2494_, 1, v_err_2483_);
                        v___x_2493_ = v_reuseFailAlloc_2494_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_err_2483_);
                    if v_isShared_2486_ == 0 {
                        crate::leanh::lean_ctor_set_tag(v___x_2485_, 0);
                        crate::leanh::lean_ctor_set(v___x_2485_, 1, v_acc_2474_);
                        v___x_2496_ = v___x_2485_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_2497_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2497_, 0, v_pos_2482_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2497_, 1, v_acc_2474_);
                        v___x_2496_ = v_reuseFailAlloc_2497_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_2493_;
            }
            3 => {
                return v___x_2496_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Internal_Parsec_manyCharsCore(
    mut v_00_u03b9_2499_: *mut crate::leanh::LeanObject,
    mut v_elem_2500_: *mut crate::leanh::LeanObject,
    mut v_idx_2501_: *mut crate::leanh::LeanObject,
    mut v_inst_2502_: *mut crate::leanh::LeanObject,
    mut v_inst_2503_: *mut crate::leanh::LeanObject,
    mut v_inst_2504_: *mut crate::leanh::LeanObject,
    mut v_p_2505_: *mut crate::leanh::LeanObject,
    mut v_acc_2506_: *mut crate::leanh::LeanObject,
    mut v_a_2507_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2508_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2508_ = l_Std_Internal_Parsec_manyCharsCore___redArg(
        v_inst_2502_,
        v_inst_2504_,
        v_p_2505_,
        v_acc_2506_,
        v_a_2507_,
    );
    return v___x_2508_;
}
pub unsafe fn l_Std_Internal_Parsec_manyCharsCore___boxed(
    mut v_00_u03b9_2509_: *mut crate::leanh::LeanObject,
    mut v_elem_2510_: *mut crate::leanh::LeanObject,
    mut v_idx_2511_: *mut crate::leanh::LeanObject,
    mut v_inst_2512_: *mut crate::leanh::LeanObject,
    mut v_inst_2513_: *mut crate::leanh::LeanObject,
    mut v_inst_2514_: *mut crate::leanh::LeanObject,
    mut v_p_2515_: *mut crate::leanh::LeanObject,
    mut v_acc_2516_: *mut crate::leanh::LeanObject,
    mut v_a_2517_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2518_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2518_ = l_Std_Internal_Parsec_manyCharsCore(
        v_00_u03b9_2509_,
        v_elem_2510_,
        v_idx_2511_,
        v_inst_2512_,
        v_inst_2513_,
        v_inst_2514_,
        v_p_2515_,
        v_acc_2516_,
        v_a_2517_,
    );
    crate::leanh::lean_dec_ref(v_inst_2513_);
    return v_res_2518_;
}
pub unsafe fn l_Std_Internal_Parsec_manyChars___redArg(
    mut v_inst_2519_: *mut crate::leanh::LeanObject,
    mut v_inst_2520_: *mut crate::leanh::LeanObject,
    mut v_p_2521_: *mut crate::leanh::LeanObject,
    mut v_a_2522_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2523_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2524_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2523_ = l_Std_Internal_Parsec_instInhabited___lam__0___closed__0;
    v___x_2524_ = l_Std_Internal_Parsec_manyCharsCore___redArg(
        v_inst_2519_,
        v_inst_2520_,
        v_p_2521_,
        v___x_2523_,
        v_a_2522_,
    );
    return v___x_2524_;
}
pub unsafe fn l_Std_Internal_Parsec_manyChars(
    mut v_00_u03b9_2525_: *mut crate::leanh::LeanObject,
    mut v_elem_2526_: *mut crate::leanh::LeanObject,
    mut v_idx_2527_: *mut crate::leanh::LeanObject,
    mut v_inst_2528_: *mut crate::leanh::LeanObject,
    mut v_inst_2529_: *mut crate::leanh::LeanObject,
    mut v_inst_2530_: *mut crate::leanh::LeanObject,
    mut v_p_2531_: *mut crate::leanh::LeanObject,
    mut v_a_2532_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2533_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2534_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2533_ = l_Std_Internal_Parsec_instInhabited___lam__0___closed__0;
    v___x_2534_ = l_Std_Internal_Parsec_manyCharsCore___redArg(
        v_inst_2528_,
        v_inst_2530_,
        v_p_2531_,
        v___x_2533_,
        v_a_2532_,
    );
    return v___x_2534_;
}
pub unsafe fn l_Std_Internal_Parsec_manyChars___boxed(
    mut v_00_u03b9_2535_: *mut crate::leanh::LeanObject,
    mut v_elem_2536_: *mut crate::leanh::LeanObject,
    mut v_idx_2537_: *mut crate::leanh::LeanObject,
    mut v_inst_2538_: *mut crate::leanh::LeanObject,
    mut v_inst_2539_: *mut crate::leanh::LeanObject,
    mut v_inst_2540_: *mut crate::leanh::LeanObject,
    mut v_p_2541_: *mut crate::leanh::LeanObject,
    mut v_a_2542_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2543_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2543_ = l_Std_Internal_Parsec_manyChars(
        v_00_u03b9_2535_,
        v_elem_2536_,
        v_idx_2537_,
        v_inst_2538_,
        v_inst_2539_,
        v_inst_2540_,
        v_p_2541_,
        v_a_2542_,
    );
    crate::leanh::lean_dec_ref(v_inst_2539_);
    return v_res_2543_;
}
pub unsafe fn l_Std_Internal_Parsec_many1Chars___redArg(
    mut v_inst_2544_: *mut crate::leanh::LeanObject,
    mut v_inst_2545_: *mut crate::leanh::LeanObject,
    mut v_p_2546_: *mut crate::leanh::LeanObject,
    mut v_a_2547_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2548_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_pos_2549_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_res_2550_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2551_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2552_: u32 = 0;
    let mut v___x_2553_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2554_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_pos_2555_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_err_2556_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2558_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2559_: u8 = 0;
    let mut v___x_2561_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2562_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2563_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                crate::leanh::lean_inc_ref(v_p_2546_);
                v___x_2548_ = crate::leanh::lean_apply_1(v_p_2546_, v_a_2547_);
                if crate::leanh::lean_obj_tag(v___x_2548_) == 0 {
                    v_pos_2549_ = crate::leanh::lean_ctor_get(v___x_2548_, 0);
                    crate::leanh::lean_inc(v_pos_2549_);
                    v_res_2550_ = crate::leanh::lean_ctor_get(v___x_2548_, 1);
                    crate::leanh::lean_inc(v_res_2550_);
                    crate::leanh::lean_dec_ref_known(v___x_2548_, 2);
                    v___x_2551_ = l_Std_Internal_Parsec_instInhabited___lam__0___closed__0;
                    v___x_2552_ = crate::leanh::lean_unbox_uint32(v_res_2550_);
                    crate::leanh::lean_dec(v_res_2550_);
                    v___x_2553_ = lean_string_push(v___x_2551_, v___x_2552_);
                    v___x_2554_ = l_Std_Internal_Parsec_manyCharsCore___redArg(
                        v_inst_2544_,
                        v_inst_2545_,
                        v_p_2546_,
                        v___x_2553_,
                        v_pos_2549_,
                    );
                    return v___x_2554_;
                } else {
                    crate::leanh::lean_dec_ref(v_p_2546_);
                    crate::leanh::lean_dec_ref(v_inst_2545_);
                    crate::leanh::lean_dec_ref(v_inst_2544_);
                    v_pos_2555_ = crate::leanh::lean_ctor_get(v___x_2548_, 0);
                    v_err_2556_ = crate::leanh::lean_ctor_get(v___x_2548_, 1);
                    v_isSharedCheck_2563_ = (!crate::leanh::lean_is_exclusive(v___x_2548_)) as u8;
                    if v_isSharedCheck_2563_ == 0 {
                        v___x_2558_ = v___x_2548_;
                        v_isShared_2559_ = v_isSharedCheck_2563_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_err_2556_);
                        crate::leanh::lean_inc(v_pos_2555_);
                        crate::leanh::lean_dec(v___x_2548_);
                        v___x_2558_ = crate::leanh::lean_box(0);
                        v_isShared_2559_ = v_isSharedCheck_2563_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_2559_ == 0 {
                    v___x_2561_ = v___x_2558_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2562_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2562_, 0, v_pos_2555_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2562_, 1, v_err_2556_);
                    v___x_2561_ = v_reuseFailAlloc_2562_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_2561_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Internal_Parsec_many1Chars(
    mut v_00_u03b9_2564_: *mut crate::leanh::LeanObject,
    mut v_elem_2565_: *mut crate::leanh::LeanObject,
    mut v_idx_2566_: *mut crate::leanh::LeanObject,
    mut v_inst_2567_: *mut crate::leanh::LeanObject,
    mut v_inst_2568_: *mut crate::leanh::LeanObject,
    mut v_inst_2569_: *mut crate::leanh::LeanObject,
    mut v_p_2570_: *mut crate::leanh::LeanObject,
    mut v_a_2571_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2572_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_pos_2573_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_res_2574_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2575_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2576_: u32 = 0;
    let mut v___x_2577_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2578_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_pos_2579_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_err_2580_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2582_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2583_: u8 = 0;
    let mut v___x_2585_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2586_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2587_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                crate::leanh::lean_inc_ref(v_p_2570_);
                v___x_2572_ = crate::leanh::lean_apply_1(v_p_2570_, v_a_2571_);
                if crate::leanh::lean_obj_tag(v___x_2572_) == 0 {
                    v_pos_2573_ = crate::leanh::lean_ctor_get(v___x_2572_, 0);
                    crate::leanh::lean_inc(v_pos_2573_);
                    v_res_2574_ = crate::leanh::lean_ctor_get(v___x_2572_, 1);
                    crate::leanh::lean_inc(v_res_2574_);
                    crate::leanh::lean_dec_ref_known(v___x_2572_, 2);
                    v___x_2575_ = l_Std_Internal_Parsec_instInhabited___lam__0___closed__0;
                    v___x_2576_ = crate::leanh::lean_unbox_uint32(v_res_2574_);
                    crate::leanh::lean_dec(v_res_2574_);
                    v___x_2577_ = lean_string_push(v___x_2575_, v___x_2576_);
                    v___x_2578_ = l_Std_Internal_Parsec_manyCharsCore___redArg(
                        v_inst_2567_,
                        v_inst_2569_,
                        v_p_2570_,
                        v___x_2577_,
                        v_pos_2573_,
                    );
                    return v___x_2578_;
                } else {
                    crate::leanh::lean_dec_ref(v_p_2570_);
                    crate::leanh::lean_dec_ref(v_inst_2569_);
                    crate::leanh::lean_dec_ref(v_inst_2567_);
                    v_pos_2579_ = crate::leanh::lean_ctor_get(v___x_2572_, 0);
                    v_err_2580_ = crate::leanh::lean_ctor_get(v___x_2572_, 1);
                    v_isSharedCheck_2587_ = (!crate::leanh::lean_is_exclusive(v___x_2572_)) as u8;
                    if v_isSharedCheck_2587_ == 0 {
                        v___x_2582_ = v___x_2572_;
                        v_isShared_2583_ = v_isSharedCheck_2587_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_err_2580_);
                        crate::leanh::lean_inc(v_pos_2579_);
                        crate::leanh::lean_dec(v___x_2572_);
                        v___x_2582_ = crate::leanh::lean_box(0);
                        v_isShared_2583_ = v_isSharedCheck_2587_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_2583_ == 0 {
                    v___x_2585_ = v___x_2582_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2586_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2586_, 0, v_pos_2579_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2586_, 1, v_err_2580_);
                    v___x_2585_ = v_reuseFailAlloc_2586_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_2585_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Internal_Parsec_many1Chars___boxed(
    mut v_00_u03b9_2588_: *mut crate::leanh::LeanObject,
    mut v_elem_2589_: *mut crate::leanh::LeanObject,
    mut v_idx_2590_: *mut crate::leanh::LeanObject,
    mut v_inst_2591_: *mut crate::leanh::LeanObject,
    mut v_inst_2592_: *mut crate::leanh::LeanObject,
    mut v_inst_2593_: *mut crate::leanh::LeanObject,
    mut v_p_2594_: *mut crate::leanh::LeanObject,
    mut v_a_2595_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2596_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2596_ = l_Std_Internal_Parsec_many1Chars(
        v_00_u03b9_2588_,
        v_elem_2589_,
        v_idx_2590_,
        v_inst_2591_,
        v_inst_2592_,
        v_inst_2593_,
        v_p_2594_,
        v_a_2595_,
    );
    crate::leanh::lean_dec_ref(v_inst_2592_);
    return v_res_2596_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Std_Internal_Parsec_Basic(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Init_NotationExtra(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_ToString_Macro(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Array_Basic(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Std_Internal_Parsec_Basic(
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
pub unsafe fn initialize_Std_Internal_Parsec_Basic(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Init_NotationExtra(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Data_ToString_Macro(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Data_Array_Basic(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Std_Internal_Parsec_Basic(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Std_Internal_Parsec_Basic(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Std_Internal_Parsec_Basic(builtin);
}
