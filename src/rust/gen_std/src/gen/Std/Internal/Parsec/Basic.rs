// Lean compiler output
// Module: Std.Internal.Parsec.Basic
// Imports: Init.NotationExtra Init.Data.ToString.Macro Init.Data.Array.Basic
use crate::ffi::{
    lean_array_push, lean_mk_empty_array_with_capacity, lean_nat_dec_le, lean_nat_to_int,
    lean_string_push,
};
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
pub static l_Std_Internal_Parsec_instReprError_repr___closed__0_value:
    leanh::LeanStringObject<30> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
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
static mut l_Std_Internal_Parsec_instReprError_repr___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Internal_Parsec_instReprError_repr___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Std_Internal_Parsec_instReprError_repr___closed__1_value:
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
        core::ptr::addr_of!(l_Std_Internal_Parsec_instReprError_repr___closed__0_value)
            as *mut leanh::LeanObject,
    ],
};
static mut l_Std_Internal_Parsec_instReprError_repr___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Internal_Parsec_instReprError_repr___closed__1_value)
        as *mut leanh::LeanObject;
static mut l_Std_Internal_Parsec_instReprError_repr___closed__2_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Internal_Parsec_instReprError_repr___closed__2: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Std_Internal_Parsec_instReprError_repr___closed__3_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Internal_Parsec_instReprError_repr___closed__3: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Std_Internal_Parsec_instReprError_repr___closed__4_value:
    leanh::LeanStringObject<32> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
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
static mut l_Std_Internal_Parsec_instReprError_repr___closed__4: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Internal_Parsec_instReprError_repr___closed__4_value)
        as *mut leanh::LeanObject;
pub static l_Std_Internal_Parsec_instReprError_repr___closed__5_value:
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
        core::ptr::addr_of!(l_Std_Internal_Parsec_instReprError_repr___closed__4_value)
            as *mut leanh::LeanObject,
    ],
};
static mut l_Std_Internal_Parsec_instReprError_repr___closed__5: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Internal_Parsec_instReprError_repr___closed__5_value)
        as *mut leanh::LeanObject;
pub static l_Std_Internal_Parsec_instReprError_repr___closed__6_value:
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
        core::ptr::addr_of!(l_Std_Internal_Parsec_instReprError_repr___closed__5_value)
            as *mut leanh::LeanObject,
        (((1 as usize) << 1) | 1) as *mut leanh::LeanObject,
    ],
};
static mut l_Std_Internal_Parsec_instReprError_repr___closed__6: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Internal_Parsec_instReprError_repr___closed__6_value)
        as *mut leanh::LeanObject;
pub static l_Std_Internal_Parsec_instReprError___closed__0_value: leanh::LeanClosureObject<
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
    m_fun: l_Std_Internal_Parsec_instReprError_repr___boxed as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Std_Internal_Parsec_instReprError___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Internal_Parsec_instReprError___closed__0_value)
        as *mut leanh::LeanObject;
pub static mut l_Std_Internal_Parsec_instReprError: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Internal_Parsec_instReprError___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Std_Internal_Parsec_instToStringError___lam__0___closed__0_value:
    leanh::LeanStringObject<24> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
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
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Internal_Parsec_instToStringError___lam__0___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Std_Internal_Parsec_instToStringError___closed__0_value:
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
    m_fun: l_Std_Internal_Parsec_instToStringError___lam__0___boxed as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Std_Internal_Parsec_instToStringError___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Internal_Parsec_instToStringError___closed__0_value)
        as *mut leanh::LeanObject;
pub static mut l_Std_Internal_Parsec_instToStringError: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Internal_Parsec_instToStringError___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Std_Internal_Parsec_instReprParseResult_repr___redArg___closed__0_value:
    leanh::LeanStringObject<40> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
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
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Internal_Parsec_instReprParseResult_repr___redArg___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Std_Internal_Parsec_instReprParseResult_repr___redArg___closed__1_value:
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
        l_Std_Internal_Parsec_instReprParseResult_repr___redArg___closed__0_value
    ) as *mut leanh::LeanObject],
};
static mut l_Std_Internal_Parsec_instReprParseResult_repr___redArg___closed__1:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Internal_Parsec_instReprParseResult_repr___redArg___closed__1_value)
        as *mut leanh::LeanObject;
pub static l_Std_Internal_Parsec_instReprParseResult_repr___redArg___closed__2_value:
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
            l_Std_Internal_Parsec_instReprParseResult_repr___redArg___closed__1_value
        ) as *mut leanh::LeanObject,
        (((1 as usize) << 1) | 1) as *mut leanh::LeanObject,
    ],
};
static mut l_Std_Internal_Parsec_instReprParseResult_repr___redArg___closed__2:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Internal_Parsec_instReprParseResult_repr___redArg___closed__2_value)
        as *mut leanh::LeanObject;
pub static l_Std_Internal_Parsec_instReprParseResult_repr___redArg___closed__3_value:
    leanh::LeanStringObject<38> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
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
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Internal_Parsec_instReprParseResult_repr___redArg___closed__3_value)
        as *mut leanh::LeanObject;
pub static l_Std_Internal_Parsec_instReprParseResult_repr___redArg___closed__4_value:
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
        l_Std_Internal_Parsec_instReprParseResult_repr___redArg___closed__3_value
    ) as *mut leanh::LeanObject],
};
static mut l_Std_Internal_Parsec_instReprParseResult_repr___redArg___closed__4:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Internal_Parsec_instReprParseResult_repr___redArg___closed__4_value)
        as *mut leanh::LeanObject;
pub static l_Std_Internal_Parsec_instReprParseResult_repr___redArg___closed__5_value:
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
            l_Std_Internal_Parsec_instReprParseResult_repr___redArg___closed__4_value
        ) as *mut leanh::LeanObject,
        (((1 as usize) << 1) | 1) as *mut leanh::LeanObject,
    ],
};
static mut l_Std_Internal_Parsec_instReprParseResult_repr___redArg___closed__5:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Internal_Parsec_instReprParseResult_repr___redArg___closed__5_value)
        as *mut leanh::LeanObject;
pub static l_Std_Internal_Parsec_instInhabited___lam__0___closed__0_value:
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
static mut l_Std_Internal_Parsec_instInhabited___lam__0___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Internal_Parsec_instInhabited___lam__0___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Std_Internal_Parsec_instInhabited___lam__0___closed__1_value:
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
        core::ptr::addr_of!(l_Std_Internal_Parsec_instInhabited___lam__0___closed__0_value)
            as *mut leanh::LeanObject,
    ],
};
static mut l_Std_Internal_Parsec_instInhabited___lam__0___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Internal_Parsec_instInhabited___lam__0___closed__1_value)
        as *mut leanh::LeanObject;
pub static l_Std_Internal_Parsec_instInhabited___closed__0_value: leanh::LeanClosureObject<
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
    m_fun: l_Std_Internal_Parsec_instInhabited___lam__0 as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Std_Internal_Parsec_instInhabited___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Internal_Parsec_instInhabited___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Std_Internal_Parsec_instMonad___closed__0_value: leanh::LeanClosureObject<0> =
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
        m_fun: l_Std_Internal_Parsec_instMonad___lam__0 as *const core::ffi::c_void,
        m_arity: 5,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Std_Internal_Parsec_instMonad___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Internal_Parsec_instMonad___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Std_Internal_Parsec_instMonad___closed__1_value: leanh::LeanClosureObject<0> =
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
        m_fun: l_Std_Internal_Parsec_instMonad___lam__1 as *const core::ffi::c_void,
        m_arity: 5,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Std_Internal_Parsec_instMonad___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Internal_Parsec_instMonad___closed__1_value)
        as *mut leanh::LeanObject;
pub static l_Std_Internal_Parsec_instMonad___closed__2_value: leanh::LeanClosureObject<0> =
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
        m_fun: l_Std_Internal_Parsec_instMonad___lam__2 as *const core::ffi::c_void,
        m_arity: 3,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Std_Internal_Parsec_instMonad___closed__2: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Internal_Parsec_instMonad___closed__2_value)
        as *mut leanh::LeanObject;
pub static l_Std_Internal_Parsec_instMonad___closed__3_value: leanh::LeanClosureObject<0> =
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
        m_fun: l_Std_Internal_Parsec_instMonad___lam__3 as *const core::ffi::c_void,
        m_arity: 5,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Std_Internal_Parsec_instMonad___closed__3: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Internal_Parsec_instMonad___closed__3_value)
        as *mut leanh::LeanObject;
pub static l_Std_Internal_Parsec_instMonad___closed__4_value: leanh::LeanClosureObject<0> =
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
        m_fun: l_Std_Internal_Parsec_instMonad___lam__4 as *const core::ffi::c_void,
        m_arity: 5,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Std_Internal_Parsec_instMonad___closed__4: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Internal_Parsec_instMonad___closed__4_value)
        as *mut leanh::LeanObject;
pub static l_Std_Internal_Parsec_instMonad___closed__5_value: leanh::LeanClosureObject<0> =
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
        m_fun: l_Std_Internal_Parsec_instMonad___lam__5 as *const core::ffi::c_void,
        m_arity: 5,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Std_Internal_Parsec_instMonad___closed__5: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Internal_Parsec_instMonad___closed__5_value)
        as *mut leanh::LeanObject;
pub static l_Std_Internal_Parsec_instMonad___closed__6_value: leanh::LeanCtorObject<2> =
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
            core::ptr::addr_of!(l_Std_Internal_Parsec_instMonad___closed__0_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Std_Internal_Parsec_instMonad___closed__1_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Std_Internal_Parsec_instMonad___closed__6: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Internal_Parsec_instMonad___closed__6_value)
        as *mut leanh::LeanObject;
pub static l_Std_Internal_Parsec_instMonad___closed__7_value: leanh::LeanCtorObject<5> =
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
            core::ptr::addr_of!(l_Std_Internal_Parsec_instMonad___closed__6_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Std_Internal_Parsec_instMonad___closed__2_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Std_Internal_Parsec_instMonad___closed__3_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Std_Internal_Parsec_instMonad___closed__4_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Std_Internal_Parsec_instMonad___closed__5_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Std_Internal_Parsec_instMonad___closed__7: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Internal_Parsec_instMonad___closed__7_value)
        as *mut leanh::LeanObject;
pub static l_Std_Internal_Parsec_instMonad___closed__8_value: leanh::LeanClosureObject<1> =
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
        m_fun: l_Std_Internal_Parsec_bind as *const core::ffi::c_void,
        m_arity: 6,
        m_num_fixed: 1,
        m_objs: [(((0 as usize) << 1) | 1) as *mut leanh::LeanObject],
    };
static mut l_Std_Internal_Parsec_instMonad___closed__8: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Internal_Parsec_instMonad___closed__8_value)
        as *mut leanh::LeanObject;
pub static l_Std_Internal_Parsec_instMonad___closed__9_value: leanh::LeanCtorObject<2> =
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
            core::ptr::addr_of!(l_Std_Internal_Parsec_instMonad___closed__7_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Std_Internal_Parsec_instMonad___closed__8_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Std_Internal_Parsec_instMonad___closed__9: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Internal_Parsec_instMonad___closed__9_value)
        as *mut leanh::LeanObject;
pub static l_Std_Internal_Parsec_instAlternative___redArg___closed__0_value:
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
    m_fun: l_Std_Internal_Parsec_instAlternative___redArg___lam__0 as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Std_Internal_Parsec_instAlternative___redArg___closed__0:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Internal_Parsec_instAlternative___redArg___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Std_Internal_Parsec_eof___redArg___closed__0_value: leanh::LeanStringObject<
    22,
> = leanh::LeanStringObject {
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
static mut l_Std_Internal_Parsec_eof___redArg___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Internal_Parsec_eof___redArg___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Std_Internal_Parsec_eof___redArg___closed__1_value: leanh::LeanCtorObject<1> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Std_Internal_Parsec_eof___redArg___closed__0_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Std_Internal_Parsec_eof___redArg___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Internal_Parsec_eof___redArg___closed__1_value)
        as *mut leanh::LeanObject;
pub static l_Std_Internal_Parsec_many___redArg___closed__0_value: leanh::LeanArrayObject<0> =
    leanh::LeanArrayObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<usize>() * 2
                + core::mem::size_of::<*mut leanh::LeanObject>() * 0)
                as u16,
            other: 0,
            tag: 246,
        },
        m_size: 0,
        m_capacity: 0,
        m_data: [],
    };
static mut l_Std_Internal_Parsec_many___redArg___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Internal_Parsec_many___redArg___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Std_Internal_Parsec_satisfy___redArg___closed__0_value:
    leanh::LeanStringObject<24> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
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
static mut l_Std_Internal_Parsec_satisfy___redArg___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Internal_Parsec_satisfy___redArg___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Std_Internal_Parsec_satisfy___redArg___closed__1_value: leanh::LeanCtorObject<
    1,
> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Std_Internal_Parsec_satisfy___redArg___closed__0_value)
            as *mut leanh::LeanObject,
    ],
};
static mut l_Std_Internal_Parsec_satisfy___redArg___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Internal_Parsec_satisfy___redArg___closed__1_value)
        as *mut leanh::LeanObject;
pub unsafe fn l_Std_Internal_Parsec_Error_ctorIdx(
    mut v_x_1299_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_x_1299_) == 0 {
        let mut v___x_1300_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_1300_ = leanh::lean_unsigned_to_nat(0);
        return v___x_1300_;
    } else {
        let mut v___x_1301_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_1301_ = leanh::lean_unsigned_to_nat(1);
        return v___x_1301_;
    }
}
pub unsafe fn l_Std_Internal_Parsec_Error_ctorIdx___boxed(
    mut v_x_1302_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1303_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1303_ = l_Std_Internal_Parsec_Error_ctorIdx(v_x_1302_);
    leanh::lean_dec(v_x_1302_);
    return v_res_1303_;
}
pub unsafe fn l_Std_Internal_Parsec_Error_ctorElim___redArg(
    mut v_t_1304_: *mut leanh::LeanObject,
    mut v_k_1305_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_t_1304_) == 0 {
        return v_k_1305_;
    } else {
        let mut v_s_1306_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1307_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_s_1306_ = leanh::lean_ctor_get(v_t_1304_, 0);
        leanh::lean_inc_ref(v_s_1306_);
        leanh::lean_dec_ref_known(v_t_1304_, 1);
        v___x_1307_ = leanh::lean_apply_1(v_k_1305_, v_s_1306_);
        return v___x_1307_;
    }
}
pub unsafe fn l_Std_Internal_Parsec_Error_ctorElim(
    mut v_motive_1308_: *mut leanh::LeanObject,
    mut v_ctorIdx_1309_: *mut leanh::LeanObject,
    mut v_t_1310_: *mut leanh::LeanObject,
    mut v_h_1311_: *mut leanh::LeanObject,
    mut v_k_1312_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1313_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1313_ = l_Std_Internal_Parsec_Error_ctorElim___redArg(v_t_1310_, v_k_1312_);
    return v___x_1313_;
}
pub unsafe fn l_Std_Internal_Parsec_Error_ctorElim___boxed(
    mut v_motive_1314_: *mut leanh::LeanObject,
    mut v_ctorIdx_1315_: *mut leanh::LeanObject,
    mut v_t_1316_: *mut leanh::LeanObject,
    mut v_h_1317_: *mut leanh::LeanObject,
    mut v_k_1318_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1319_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1319_ = l_Std_Internal_Parsec_Error_ctorElim(
        v_motive_1314_,
        v_ctorIdx_1315_,
        v_t_1316_,
        v_h_1317_,
        v_k_1318_,
    );
    leanh::lean_dec(v_ctorIdx_1315_);
    return v_res_1319_;
}
pub unsafe fn l_Std_Internal_Parsec_Error_eof_elim___redArg(
    mut v_t_1320_: *mut leanh::LeanObject,
    mut v_eof_1321_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1322_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1322_ = l_Std_Internal_Parsec_Error_ctorElim___redArg(v_t_1320_, v_eof_1321_);
    return v___x_1322_;
}
pub unsafe fn l_Std_Internal_Parsec_Error_eof_elim(
    mut v_motive_1323_: *mut leanh::LeanObject,
    mut v_t_1324_: *mut leanh::LeanObject,
    mut v_h_1325_: *mut leanh::LeanObject,
    mut v_eof_1326_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1327_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1327_ = l_Std_Internal_Parsec_Error_ctorElim___redArg(v_t_1324_, v_eof_1326_);
    return v___x_1327_;
}
pub unsafe fn l_Std_Internal_Parsec_Error_other_elim___redArg(
    mut v_t_1328_: *mut leanh::LeanObject,
    mut v_other_1329_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1330_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1330_ = l_Std_Internal_Parsec_Error_ctorElim___redArg(v_t_1328_, v_other_1329_);
    return v___x_1330_;
}
pub unsafe fn l_Std_Internal_Parsec_Error_other_elim(
    mut v_motive_1331_: *mut leanh::LeanObject,
    mut v_t_1332_: *mut leanh::LeanObject,
    mut v_h_1333_: *mut leanh::LeanObject,
    mut v_other_1334_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1335_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1335_ = l_Std_Internal_Parsec_Error_ctorElim___redArg(v_t_1332_, v_other_1334_);
    return v___x_1335_;
}
pub unsafe fn _init_l_Std_Internal_Parsec_instReprError_repr___closed__2()
-> *mut leanh::LeanObject {
    let mut v___x_1339_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1340_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1339_ = leanh::lean_unsigned_to_nat(2);
    v___x_1340_ = lean_nat_to_int(v___x_1339_);
    return v___x_1340_;
}
pub unsafe fn _init_l_Std_Internal_Parsec_instReprError_repr___closed__3()
-> *mut leanh::LeanObject {
    let mut v___x_1341_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1342_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1341_ = leanh::lean_unsigned_to_nat(1);
    v___x_1342_ = lean_nat_to_int(v___x_1341_);
    return v___x_1342_;
}
pub unsafe fn l_Std_Internal_Parsec_instReprError_repr(
    mut v_x_1349_: *mut leanh::LeanObject,
    mut v_prec_1350_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___y_1352_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1353_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1354_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1355_: u8 = 0;
    let mut v___x_1356_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1357_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1358_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1359_: u8 = 0;
    let mut v___x_1360_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1361_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_s_1362_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1364_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1365_: u8 = 0;
    let mut v___y_1367_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1368_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1369_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1371_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1372_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1373_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1374_: u8 = 0;
    let mut v___x_1375_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1376_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1377_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1378_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1379_: u8 = 0;
    let mut v___x_1380_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1381_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1382_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_1349_) == 0 {
                    v___x_1358_ = leanh::lean_unsigned_to_nat(1024);
                    v___x_1359_ = lean_nat_dec_le(v___x_1358_, v_prec_1350_);
                    if v___x_1359_ == 0 {
                        v___x_1360_ = leanh::lean_obj_once(
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
                        v___x_1361_ = leanh::lean_obj_once(
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
                    v_s_1362_ = leanh::lean_ctor_get(v_x_1349_, 0);
                    v_isSharedCheck_1382_ = (!leanh::lean_is_exclusive(v_x_1349_)) as u8;
                    if v_isSharedCheck_1382_ == 0 {
                        v___x_1364_ = v_x_1349_;
                        v_isShared_1365_ = v_isSharedCheck_1382_;
                        state = 2;
                        continue;
                    } else {
                        leanh::lean_inc(v_s_1362_);
                        leanh::lean_dec(v_x_1349_);
                        v___x_1364_ = leanh::lean_box(0);
                        v_isShared_1365_ = v_isSharedCheck_1382_;
                        state = 2;
                        continue;
                    }
                }
            }
            1 => {
                v___x_1353_ = l_Std_Internal_Parsec_instReprError_repr___closed__1;
                leanh::lean_inc(v___y_1352_);
                v___x_1354_ = leanh::lean_alloc_ctor(4, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_1354_, 0, v___y_1352_);
                leanh::lean_ctor_set(v___x_1354_, 1, v___x_1353_);
                v___x_1355_ = 0;
                v___x_1356_ = leanh::lean_alloc_ctor(6, 1, (1) as u32);
                leanh::lean_ctor_set(v___x_1356_, 0, v___x_1354_);
                leanh::lean_ctor_set_uint8(
                    v___x_1356_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                    v___x_1355_,
                );
                v___x_1357_ = l_Repr_addAppParen(v___x_1356_, v_prec_1350_);
                return v___x_1357_;
            }
            2 => {
                v___x_1378_ = leanh::lean_unsigned_to_nat(1024);
                v___x_1379_ = lean_nat_dec_le(v___x_1378_, v_prec_1350_);
                if v___x_1379_ == 0 {
                    v___x_1380_ = leanh::lean_obj_once(
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
                    v___x_1381_ = leanh::lean_obj_once(
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
                    leanh::lean_ctor_set_tag(v___x_1364_, 3);
                    leanh::lean_ctor_set(v___x_1364_, 0, v___x_1369_);
                    v___x_1371_ = v___x_1364_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1377_ = leanh::lean_alloc_ctor(3, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1377_, 0, v___x_1369_);
                    v___x_1371_ = v_reuseFailAlloc_1377_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_1372_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_1372_, 0, v___x_1368_);
                leanh::lean_ctor_set(v___x_1372_, 1, v___x_1371_);
                leanh::lean_inc(v___y_1367_);
                v___x_1373_ = leanh::lean_alloc_ctor(4, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_1373_, 0, v___y_1367_);
                leanh::lean_ctor_set(v___x_1373_, 1, v___x_1372_);
                v___x_1374_ = 0;
                v___x_1375_ = leanh::lean_alloc_ctor(6, 1, (1) as u32);
                leanh::lean_ctor_set(v___x_1375_, 0, v___x_1373_);
                leanh::lean_ctor_set_uint8(
                    v___x_1375_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
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
    mut v_x_1383_: *mut leanh::LeanObject,
    mut v_prec_1384_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1385_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1385_ = l_Std_Internal_Parsec_instReprError_repr(v_x_1383_, v_prec_1384_);
    leanh::lean_dec(v_prec_1384_);
    return v_res_1385_;
}
pub unsafe fn l_Std_Internal_Parsec_instToStringError___lam__0(
    mut v_x_1389_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_x_1389_) == 0 {
        let mut v___x_1390_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_1390_ = l_Std_Internal_Parsec_instToStringError___lam__0___closed__0;
        return v___x_1390_;
    } else {
        let mut v_s_1391_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_s_1391_ = leanh::lean_ctor_get(v_x_1389_, 0);
        leanh::lean_inc_ref(v_s_1391_);
        return v_s_1391_;
    }
}
pub unsafe fn l_Std_Internal_Parsec_instToStringError___lam__0___boxed(
    mut v_x_1392_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1393_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1393_ = l_Std_Internal_Parsec_instToStringError___lam__0(v_x_1392_);
    leanh::lean_dec(v_x_1392_);
    return v_res_1393_;
}
pub unsafe fn l_Std_Internal_Parsec_ParseResult_ctorIdx___redArg(
    mut v_x_1396_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_x_1396_) == 0 {
        let mut v___x_1397_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_1397_ = leanh::lean_unsigned_to_nat(0);
        return v___x_1397_;
    } else {
        let mut v___x_1398_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_1398_ = leanh::lean_unsigned_to_nat(1);
        return v___x_1398_;
    }
}
pub unsafe fn l_Std_Internal_Parsec_ParseResult_ctorIdx___redArg___boxed(
    mut v_x_1399_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1400_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1400_ = l_Std_Internal_Parsec_ParseResult_ctorIdx___redArg(v_x_1399_);
    leanh::lean_dec_ref(v_x_1399_);
    return v_res_1400_;
}
pub unsafe fn l_Std_Internal_Parsec_ParseResult_ctorIdx(
    mut v_00_u03b1_1401_: *mut leanh::LeanObject,
    mut v_00_u03b9_1402_: *mut leanh::LeanObject,
    mut v_x_1403_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1404_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1404_ = l_Std_Internal_Parsec_ParseResult_ctorIdx___redArg(v_x_1403_);
    return v___x_1404_;
}
pub unsafe fn l_Std_Internal_Parsec_ParseResult_ctorIdx___boxed(
    mut v_00_u03b1_1405_: *mut leanh::LeanObject,
    mut v_00_u03b9_1406_: *mut leanh::LeanObject,
    mut v_x_1407_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1408_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1408_ =
        l_Std_Internal_Parsec_ParseResult_ctorIdx(v_00_u03b1_1405_, v_00_u03b9_1406_, v_x_1407_);
    leanh::lean_dec_ref(v_x_1407_);
    return v_res_1408_;
}
pub unsafe fn l_Std_Internal_Parsec_ParseResult_ctorElim___redArg(
    mut v_t_1409_: *mut leanh::LeanObject,
    mut v_k_1410_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_pos_1411_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_res_1412_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1413_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_pos_1411_ = leanh::lean_ctor_get(v_t_1409_, 0);
    leanh::lean_inc(v_pos_1411_);
    v_res_1412_ = leanh::lean_ctor_get(v_t_1409_, 1);
    leanh::lean_inc(v_res_1412_);
    leanh::lean_dec_ref(v_t_1409_);
    v___x_1413_ = leanh::lean_apply_2(v_k_1410_, v_pos_1411_, v_res_1412_);
    return v___x_1413_;
}
pub unsafe fn l_Std_Internal_Parsec_ParseResult_ctorElim(
    mut v_00_u03b1_1414_: *mut leanh::LeanObject,
    mut v_00_u03b9_1415_: *mut leanh::LeanObject,
    mut v_motive_1416_: *mut leanh::LeanObject,
    mut v_ctorIdx_1417_: *mut leanh::LeanObject,
    mut v_t_1418_: *mut leanh::LeanObject,
    mut v_h_1419_: *mut leanh::LeanObject,
    mut v_k_1420_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1421_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1421_ = l_Std_Internal_Parsec_ParseResult_ctorElim___redArg(v_t_1418_, v_k_1420_);
    return v___x_1421_;
}
pub unsafe fn l_Std_Internal_Parsec_ParseResult_ctorElim___boxed(
    mut v_00_u03b1_1422_: *mut leanh::LeanObject,
    mut v_00_u03b9_1423_: *mut leanh::LeanObject,
    mut v_motive_1424_: *mut leanh::LeanObject,
    mut v_ctorIdx_1425_: *mut leanh::LeanObject,
    mut v_t_1426_: *mut leanh::LeanObject,
    mut v_h_1427_: *mut leanh::LeanObject,
    mut v_k_1428_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1429_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1429_ = l_Std_Internal_Parsec_ParseResult_ctorElim(
        v_00_u03b1_1422_,
        v_00_u03b9_1423_,
        v_motive_1424_,
        v_ctorIdx_1425_,
        v_t_1426_,
        v_h_1427_,
        v_k_1428_,
    );
    leanh::lean_dec(v_ctorIdx_1425_);
    return v_res_1429_;
}
pub unsafe fn l_Std_Internal_Parsec_ParseResult_success_elim___redArg(
    mut v_t_1430_: *mut leanh::LeanObject,
    mut v_success_1431_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1432_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1432_ = l_Std_Internal_Parsec_ParseResult_ctorElim___redArg(v_t_1430_, v_success_1431_);
    return v___x_1432_;
}
pub unsafe fn l_Std_Internal_Parsec_ParseResult_success_elim(
    mut v_00_u03b1_1433_: *mut leanh::LeanObject,
    mut v_00_u03b9_1434_: *mut leanh::LeanObject,
    mut v_motive_1435_: *mut leanh::LeanObject,
    mut v_t_1436_: *mut leanh::LeanObject,
    mut v_h_1437_: *mut leanh::LeanObject,
    mut v_success_1438_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1439_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1439_ = l_Std_Internal_Parsec_ParseResult_ctorElim___redArg(v_t_1436_, v_success_1438_);
    return v___x_1439_;
}
pub unsafe fn l_Std_Internal_Parsec_ParseResult_error_elim___redArg(
    mut v_t_1440_: *mut leanh::LeanObject,
    mut v_error_1441_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1442_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1442_ = l_Std_Internal_Parsec_ParseResult_ctorElim___redArg(v_t_1440_, v_error_1441_);
    return v___x_1442_;
}
pub unsafe fn l_Std_Internal_Parsec_ParseResult_error_elim(
    mut v_00_u03b1_1443_: *mut leanh::LeanObject,
    mut v_00_u03b9_1444_: *mut leanh::LeanObject,
    mut v_motive_1445_: *mut leanh::LeanObject,
    mut v_t_1446_: *mut leanh::LeanObject,
    mut v_h_1447_: *mut leanh::LeanObject,
    mut v_error_1448_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1449_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1449_ = l_Std_Internal_Parsec_ParseResult_ctorElim___redArg(v_t_1446_, v_error_1448_);
    return v___x_1449_;
}
pub unsafe fn l_Std_Internal_Parsec_instReprParseResult_repr___redArg(
    mut v_inst_1462_: *mut leanh::LeanObject,
    mut v_inst_1463_: *mut leanh::LeanObject,
    mut v_x_1464_: *mut leanh::LeanObject,
    mut v_prec_1465_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_pos_1466_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_res_1467_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1469_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1470_: u8 = 0;
    let mut v___y_1472_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1473_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1474_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1475_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1476_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1478_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1479_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1480_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1481_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1482_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1483_: u8 = 0;
    let mut v___x_1484_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1485_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1486_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1487_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1488_: u8 = 0;
    let mut v___x_1489_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1490_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1491_: u8 = 0;
    let mut v_pos_1492_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_err_1493_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1495_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1496_: u8 = 0;
    let mut v___y_1498_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1499_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1500_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1501_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1502_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1504_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1505_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1506_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1507_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1508_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1509_: u8 = 0;
    let mut v___x_1510_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1511_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1512_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1513_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1514_: u8 = 0;
    let mut v___x_1515_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1516_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1517_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_1464_) == 0 {
                    v_pos_1466_ = leanh::lean_ctor_get(v_x_1464_, 0);
                    v_res_1467_ = leanh::lean_ctor_get(v_x_1464_, 1);
                    v_isSharedCheck_1491_ = (!leanh::lean_is_exclusive(v_x_1464_)) as u8;
                    if v_isSharedCheck_1491_ == 0 {
                        v___x_1469_ = v_x_1464_;
                        v_isShared_1470_ = v_isSharedCheck_1491_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_res_1467_);
                        leanh::lean_inc(v_pos_1466_);
                        leanh::lean_dec(v_x_1464_);
                        v___x_1469_ = leanh::lean_box(0);
                        v_isShared_1470_ = v_isSharedCheck_1491_;
                        state = 1;
                        continue;
                    }
                } else {
                    leanh::lean_dec_ref(v_inst_1462_);
                    v_pos_1492_ = leanh::lean_ctor_get(v_x_1464_, 0);
                    v_err_1493_ = leanh::lean_ctor_get(v_x_1464_, 1);
                    v_isSharedCheck_1517_ = (!leanh::lean_is_exclusive(v_x_1464_)) as u8;
                    if v_isSharedCheck_1517_ == 0 {
                        v___x_1495_ = v_x_1464_;
                        v_isShared_1496_ = v_isSharedCheck_1517_;
                        state = 4;
                        continue;
                    } else {
                        leanh::lean_inc(v_err_1493_);
                        leanh::lean_inc(v_pos_1492_);
                        leanh::lean_dec(v_x_1464_);
                        v___x_1495_ = leanh::lean_box(0);
                        v_isShared_1496_ = v_isSharedCheck_1517_;
                        state = 4;
                        continue;
                    }
                }
            }
            1 => {
                v___x_1487_ = leanh::lean_unsigned_to_nat(1024);
                v___x_1488_ = lean_nat_dec_le(v___x_1487_, v_prec_1465_);
                if v___x_1488_ == 0 {
                    v___x_1489_ = leanh::lean_obj_once(
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
                    v___x_1490_ = leanh::lean_obj_once(
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
                v___x_1473_ = leanh::lean_box(1);
                v___x_1474_ = l_Std_Internal_Parsec_instReprParseResult_repr___redArg___closed__2;
                v___x_1475_ = leanh::lean_unsigned_to_nat(1024);
                v___x_1476_ = leanh::lean_apply_2(v_inst_1463_, v_pos_1466_, v___x_1475_);
                if v_isShared_1470_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_1469_, 5);
                    leanh::lean_ctor_set(v___x_1469_, 1, v___x_1476_);
                    leanh::lean_ctor_set(v___x_1469_, 0, v___x_1474_);
                    v___x_1478_ = v___x_1469_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_1486_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1486_, 0, v___x_1474_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1486_, 1, v___x_1476_);
                    v___x_1478_ = v_reuseFailAlloc_1486_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_1479_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_1479_, 0, v___x_1478_);
                leanh::lean_ctor_set(v___x_1479_, 1, v___x_1473_);
                v___x_1480_ = leanh::lean_apply_2(v_inst_1462_, v_res_1467_, v___x_1475_);
                v___x_1481_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_1481_, 0, v___x_1479_);
                leanh::lean_ctor_set(v___x_1481_, 1, v___x_1480_);
                leanh::lean_inc(v___y_1472_);
                v___x_1482_ = leanh::lean_alloc_ctor(4, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_1482_, 0, v___y_1472_);
                leanh::lean_ctor_set(v___x_1482_, 1, v___x_1481_);
                v___x_1483_ = 0;
                v___x_1484_ = leanh::lean_alloc_ctor(6, 1, (1) as u32);
                leanh::lean_ctor_set(v___x_1484_, 0, v___x_1482_);
                leanh::lean_ctor_set_uint8(
                    v___x_1484_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                    v___x_1483_,
                );
                v___x_1485_ = l_Repr_addAppParen(v___x_1484_, v_prec_1465_);
                return v___x_1485_;
            }
            4 => {
                v___x_1513_ = leanh::lean_unsigned_to_nat(1024);
                v___x_1514_ = lean_nat_dec_le(v___x_1513_, v_prec_1465_);
                if v___x_1514_ == 0 {
                    v___x_1515_ = leanh::lean_obj_once(
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
                    v___x_1516_ = leanh::lean_obj_once(
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
                v___x_1499_ = leanh::lean_box(1);
                v___x_1500_ = l_Std_Internal_Parsec_instReprParseResult_repr___redArg___closed__5;
                v___x_1501_ = leanh::lean_unsigned_to_nat(1024);
                v___x_1502_ = leanh::lean_apply_2(v_inst_1463_, v_pos_1492_, v___x_1501_);
                if v_isShared_1496_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_1495_, 5);
                    leanh::lean_ctor_set(v___x_1495_, 1, v___x_1502_);
                    leanh::lean_ctor_set(v___x_1495_, 0, v___x_1500_);
                    v___x_1504_ = v___x_1495_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_1512_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1512_, 0, v___x_1500_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1512_, 1, v___x_1502_);
                    v___x_1504_ = v_reuseFailAlloc_1512_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                v___x_1505_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_1505_, 0, v___x_1504_);
                leanh::lean_ctor_set(v___x_1505_, 1, v___x_1499_);
                v___x_1506_ = l_Std_Internal_Parsec_instReprError_repr(v_err_1493_, v___x_1501_);
                v___x_1507_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_1507_, 0, v___x_1505_);
                leanh::lean_ctor_set(v___x_1507_, 1, v___x_1506_);
                leanh::lean_inc(v___y_1498_);
                v___x_1508_ = leanh::lean_alloc_ctor(4, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_1508_, 0, v___y_1498_);
                leanh::lean_ctor_set(v___x_1508_, 1, v___x_1507_);
                v___x_1509_ = 0;
                v___x_1510_ = leanh::lean_alloc_ctor(6, 1, (1) as u32);
                leanh::lean_ctor_set(v___x_1510_, 0, v___x_1508_);
                leanh::lean_ctor_set_uint8(
                    v___x_1510_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
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
    mut v_inst_1518_: *mut leanh::LeanObject,
    mut v_inst_1519_: *mut leanh::LeanObject,
    mut v_x_1520_: *mut leanh::LeanObject,
    mut v_prec_1521_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1522_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1522_ = l_Std_Internal_Parsec_instReprParseResult_repr___redArg(
        v_inst_1518_,
        v_inst_1519_,
        v_x_1520_,
        v_prec_1521_,
    );
    leanh::lean_dec(v_prec_1521_);
    return v_res_1522_;
}
pub unsafe fn l_Std_Internal_Parsec_instReprParseResult_repr(
    mut v_00_u03b1_1523_: *mut leanh::LeanObject,
    mut v_00_u03b9_1524_: *mut leanh::LeanObject,
    mut v_inst_1525_: *mut leanh::LeanObject,
    mut v_inst_1526_: *mut leanh::LeanObject,
    mut v_x_1527_: *mut leanh::LeanObject,
    mut v_prec_1528_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1529_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1529_ = l_Std_Internal_Parsec_instReprParseResult_repr___redArg(
        v_inst_1525_,
        v_inst_1526_,
        v_x_1527_,
        v_prec_1528_,
    );
    return v___x_1529_;
}
pub unsafe fn l_Std_Internal_Parsec_instReprParseResult_repr___boxed(
    mut v_00_u03b1_1530_: *mut leanh::LeanObject,
    mut v_00_u03b9_1531_: *mut leanh::LeanObject,
    mut v_inst_1532_: *mut leanh::LeanObject,
    mut v_inst_1533_: *mut leanh::LeanObject,
    mut v_x_1534_: *mut leanh::LeanObject,
    mut v_prec_1535_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1536_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1536_ = l_Std_Internal_Parsec_instReprParseResult_repr(
        v_00_u03b1_1530_,
        v_00_u03b9_1531_,
        v_inst_1532_,
        v_inst_1533_,
        v_x_1534_,
        v_prec_1535_,
    );
    leanh::lean_dec(v_prec_1535_);
    return v_res_1536_;
}
pub unsafe fn l_Std_Internal_Parsec_instReprParseResult___redArg(
    mut v_inst_1537_: *mut leanh::LeanObject,
    mut v_inst_1538_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1539_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1539_ = leanh::lean_alloc_closure(
        l_Std_Internal_Parsec_instReprParseResult_repr___boxed as *mut core::ffi::c_void,
        6,
        4,
    );
    leanh::lean_closure_set(v___x_1539_, 0, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_1539_, 1, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_1539_, 2, v_inst_1537_);
    leanh::lean_closure_set(v___x_1539_, 3, v_inst_1538_);
    return v___x_1539_;
}
pub unsafe fn l_Std_Internal_Parsec_instReprParseResult(
    mut v_00_u03b1_1540_: *mut leanh::LeanObject,
    mut v_00_u03b9_1541_: *mut leanh::LeanObject,
    mut v_inst_1542_: *mut leanh::LeanObject,
    mut v_inst_1543_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1544_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1544_ = leanh::lean_alloc_closure(
        l_Std_Internal_Parsec_instReprParseResult_repr___boxed as *mut core::ffi::c_void,
        6,
        4,
    );
    leanh::lean_closure_set(v___x_1544_, 0, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_1544_, 1, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_1544_, 2, v_inst_1542_);
    leanh::lean_closure_set(v___x_1544_, 3, v_inst_1543_);
    return v___x_1544_;
}
pub unsafe fn l_Std_Internal_Parsec_instInhabited___lam__0(
    mut v_it_1548_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1549_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1550_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1549_ = l_Std_Internal_Parsec_instInhabited___lam__0___closed__1;
    v___x_1550_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_1550_, 0, v_it_1548_);
    leanh::lean_ctor_set(v___x_1550_, 1, v___x_1549_);
    return v___x_1550_;
}
pub unsafe fn l_Std_Internal_Parsec_instInhabited(
    mut v_00_u03b1_1552_: *mut leanh::LeanObject,
    mut v_00_u03b9_1553_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_1554_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_1554_ = l_Std_Internal_Parsec_instInhabited___closed__0;
    return v___f_1554_;
}
pub unsafe fn l_Std_Internal_Parsec_pure___redArg(
    mut v_a_1555_: *mut leanh::LeanObject,
    mut v_it_1556_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1557_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1557_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_1557_, 0, v_it_1556_);
    leanh::lean_ctor_set(v___x_1557_, 1, v_a_1555_);
    return v___x_1557_;
}
pub unsafe fn l_Std_Internal_Parsec_pure(
    mut v_00_u03b1_1558_: *mut leanh::LeanObject,
    mut v_00_u03b9_1559_: *mut leanh::LeanObject,
    mut v_a_1560_: *mut leanh::LeanObject,
    mut v_it_1561_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1562_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1562_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_1562_, 0, v_it_1561_);
    leanh::lean_ctor_set(v___x_1562_, 1, v_a_1560_);
    return v___x_1562_;
}
pub unsafe fn l_Std_Internal_Parsec_bind___redArg(
    mut v_f_1563_: *mut leanh::LeanObject,
    mut v_g_1564_: *mut leanh::LeanObject,
    mut v_it_1565_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1566_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_pos_1567_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_res_1568_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1569_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_pos_1570_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_err_1571_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1573_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1574_: u8 = 0;
    let mut v___x_1576_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1577_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1578_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1566_ = leanh::lean_apply_1(v_f_1563_, v_it_1565_);
                if leanh::lean_obj_tag(v___x_1566_) == 0 {
                    v_pos_1567_ = leanh::lean_ctor_get(v___x_1566_, 0);
                    leanh::lean_inc(v_pos_1567_);
                    v_res_1568_ = leanh::lean_ctor_get(v___x_1566_, 1);
                    leanh::lean_inc(v_res_1568_);
                    leanh::lean_dec_ref_known(v___x_1566_, 2);
                    v___x_1569_ = leanh::lean_apply_2(v_g_1564_, v_res_1568_, v_pos_1567_);
                    return v___x_1569_;
                } else {
                    leanh::lean_dec_ref(v_g_1564_);
                    v_pos_1570_ = leanh::lean_ctor_get(v___x_1566_, 0);
                    v_err_1571_ = leanh::lean_ctor_get(v___x_1566_, 1);
                    v_isSharedCheck_1578_ = (!leanh::lean_is_exclusive(v___x_1566_)) as u8;
                    if v_isSharedCheck_1578_ == 0 {
                        v___x_1573_ = v___x_1566_;
                        v_isShared_1574_ = v_isSharedCheck_1578_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_err_1571_);
                        leanh::lean_inc(v_pos_1570_);
                        leanh::lean_dec(v___x_1566_);
                        v___x_1573_ = leanh::lean_box(0);
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
                    v_reuseFailAlloc_1577_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1577_, 0, v_pos_1570_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1577_, 1, v_err_1571_);
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
    mut v_00_u03b9_1579_: *mut leanh::LeanObject,
    mut v_00_u03b1_1580_: *mut leanh::LeanObject,
    mut v_00_u03b2_1581_: *mut leanh::LeanObject,
    mut v_f_1582_: *mut leanh::LeanObject,
    mut v_g_1583_: *mut leanh::LeanObject,
    mut v_it_1584_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1585_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_pos_1586_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_res_1587_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1588_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_pos_1589_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_err_1590_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1592_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1593_: u8 = 0;
    let mut v___x_1595_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1596_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1597_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1585_ = leanh::lean_apply_1(v_f_1582_, v_it_1584_);
                if leanh::lean_obj_tag(v___x_1585_) == 0 {
                    v_pos_1586_ = leanh::lean_ctor_get(v___x_1585_, 0);
                    leanh::lean_inc(v_pos_1586_);
                    v_res_1587_ = leanh::lean_ctor_get(v___x_1585_, 1);
                    leanh::lean_inc(v_res_1587_);
                    leanh::lean_dec_ref_known(v___x_1585_, 2);
                    v___x_1588_ = leanh::lean_apply_2(v_g_1583_, v_res_1587_, v_pos_1586_);
                    return v___x_1588_;
                } else {
                    leanh::lean_dec_ref(v_g_1583_);
                    v_pos_1589_ = leanh::lean_ctor_get(v___x_1585_, 0);
                    v_err_1590_ = leanh::lean_ctor_get(v___x_1585_, 1);
                    v_isSharedCheck_1597_ = (!leanh::lean_is_exclusive(v___x_1585_)) as u8;
                    if v_isSharedCheck_1597_ == 0 {
                        v___x_1592_ = v___x_1585_;
                        v_isShared_1593_ = v_isSharedCheck_1597_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_err_1590_);
                        leanh::lean_inc(v_pos_1589_);
                        leanh::lean_dec(v___x_1585_);
                        v___x_1592_ = leanh::lean_box(0);
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
                    v_reuseFailAlloc_1596_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1596_, 0, v_pos_1589_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1596_, 1, v_err_1590_);
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
    mut v_msg_1598_: *mut leanh::LeanObject,
    mut v_it_1599_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1600_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1601_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1600_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_1600_, 0, v_msg_1598_);
    v___x_1601_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_1601_, 0, v_it_1599_);
    leanh::lean_ctor_set(v___x_1601_, 1, v___x_1600_);
    return v___x_1601_;
}
pub unsafe fn l_Std_Internal_Parsec_fail(
    mut v_00_u03b1_1602_: *mut leanh::LeanObject,
    mut v_00_u03b9_1603_: *mut leanh::LeanObject,
    mut v_msg_1604_: *mut leanh::LeanObject,
    mut v_it_1605_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1606_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1607_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1606_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_1606_, 0, v_msg_1604_);
    v___x_1607_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_1607_, 0, v_it_1605_);
    leanh::lean_ctor_set(v___x_1607_, 1, v___x_1606_);
    return v___x_1607_;
}
pub unsafe fn l_Std_Internal_Parsec_tryCatch___redArg(
    mut v_inst_1608_: *mut leanh::LeanObject,
    mut v_inst_1609_: *mut leanh::LeanObject,
    mut v_p_1610_: *mut leanh::LeanObject,
    mut v_csuccess_1611_: *mut leanh::LeanObject,
    mut v_cerror_1612_: *mut leanh::LeanObject,
    mut v_it_1613_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1614_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_pos_1615_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_res_1616_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1617_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_pos_1618_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_err_1619_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1621_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1622_: u8 = 0;
    let mut v_pos_1623_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1624_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1625_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1626_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1627_: u8 = 0;
    let mut v___x_1629_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1630_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1631_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1632_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1633_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                leanh::lean_inc(v_it_1613_);
                v___x_1614_ = leanh::lean_apply_1(v_p_1610_, v_it_1613_);
                if leanh::lean_obj_tag(v___x_1614_) == 0 {
                    leanh::lean_dec(v_it_1613_);
                    leanh::lean_dec_ref(v_cerror_1612_);
                    leanh::lean_dec_ref(v_inst_1609_);
                    leanh::lean_dec_ref(v_inst_1608_);
                    v_pos_1615_ = leanh::lean_ctor_get(v___x_1614_, 0);
                    leanh::lean_inc(v_pos_1615_);
                    v_res_1616_ = leanh::lean_ctor_get(v___x_1614_, 1);
                    leanh::lean_inc(v_res_1616_);
                    leanh::lean_dec_ref_known(v___x_1614_, 2);
                    v___x_1617_ =
                        leanh::lean_apply_2(v_csuccess_1611_, v_res_1616_, v_pos_1615_);
                    return v___x_1617_;
                } else {
                    leanh::lean_dec_ref(v_csuccess_1611_);
                    v_pos_1618_ = leanh::lean_ctor_get(v___x_1614_, 0);
                    v_err_1619_ = leanh::lean_ctor_get(v___x_1614_, 1);
                    v_isSharedCheck_1633_ = (!leanh::lean_is_exclusive(v___x_1614_)) as u8;
                    if v_isSharedCheck_1633_ == 0 {
                        v___x_1621_ = v___x_1614_;
                        v_isShared_1622_ = v_isSharedCheck_1633_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_err_1619_);
                        leanh::lean_inc(v_pos_1618_);
                        leanh::lean_dec(v___x_1614_);
                        v___x_1621_ = leanh::lean_box(0);
                        v_isShared_1622_ = v_isSharedCheck_1633_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v_pos_1623_ = leanh::lean_ctor_get(v_inst_1609_, 0);
                leanh::lean_inc_n(v_pos_1623_, 2);
                leanh::lean_dec_ref(v_inst_1609_);
                v___x_1624_ = leanh::lean_apply_1(v_pos_1623_, v_it_1613_);
                leanh::lean_inc(v_pos_1618_);
                v___x_1625_ = leanh::lean_apply_1(v_pos_1623_, v_pos_1618_);
                v___x_1626_ = leanh::lean_apply_2(v_inst_1608_, v___x_1624_, v___x_1625_);
                v___x_1627_ = (leanh::lean_unbox(v___x_1626_) as u8);
                if v___x_1627_ == 0 {
                    leanh::lean_dec_ref(v_cerror_1612_);
                    if v_isShared_1622_ == 0 {
                        v___x_1629_ = v___x_1621_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_1630_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_1630_, 0, v_pos_1618_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_1630_, 1, v_err_1619_);
                        v___x_1629_ = v_reuseFailAlloc_1630_;
                        state = 2;
                        continue;
                    }
                } else {
                    leanh::lean_del_object(v___x_1621_);
                    leanh::lean_dec(v_err_1619_);
                    v___x_1631_ = leanh::lean_box(0);
                    v___x_1632_ =
                        leanh::lean_apply_2(v_cerror_1612_, v___x_1631_, v_pos_1618_);
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
    mut v_00_u03b1_1634_: *mut leanh::LeanObject,
    mut v_00_u03b9_1635_: *mut leanh::LeanObject,
    mut v_elem_1636_: *mut leanh::LeanObject,
    mut v_idx_1637_: *mut leanh::LeanObject,
    mut v_inst_1638_: *mut leanh::LeanObject,
    mut v_inst_1639_: *mut leanh::LeanObject,
    mut v_inst_1640_: *mut leanh::LeanObject,
    mut v_00_u03b2_1641_: *mut leanh::LeanObject,
    mut v_p_1642_: *mut leanh::LeanObject,
    mut v_csuccess_1643_: *mut leanh::LeanObject,
    mut v_cerror_1644_: *mut leanh::LeanObject,
    mut v_it_1645_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1646_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_pos_1647_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_res_1648_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1649_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_pos_1650_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_err_1651_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1653_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1654_: u8 = 0;
    let mut v_pos_1655_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1656_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1657_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1658_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1659_: u8 = 0;
    let mut v___x_1661_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1662_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1663_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1664_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1665_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                leanh::lean_inc(v_it_1645_);
                v___x_1646_ = leanh::lean_apply_1(v_p_1642_, v_it_1645_);
                if leanh::lean_obj_tag(v___x_1646_) == 0 {
                    leanh::lean_dec(v_it_1645_);
                    leanh::lean_dec_ref(v_cerror_1644_);
                    leanh::lean_dec_ref(v_inst_1640_);
                    leanh::lean_dec_ref(v_inst_1638_);
                    v_pos_1647_ = leanh::lean_ctor_get(v___x_1646_, 0);
                    leanh::lean_inc(v_pos_1647_);
                    v_res_1648_ = leanh::lean_ctor_get(v___x_1646_, 1);
                    leanh::lean_inc(v_res_1648_);
                    leanh::lean_dec_ref_known(v___x_1646_, 2);
                    v___x_1649_ =
                        leanh::lean_apply_2(v_csuccess_1643_, v_res_1648_, v_pos_1647_);
                    return v___x_1649_;
                } else {
                    leanh::lean_dec_ref(v_csuccess_1643_);
                    v_pos_1650_ = leanh::lean_ctor_get(v___x_1646_, 0);
                    v_err_1651_ = leanh::lean_ctor_get(v___x_1646_, 1);
                    v_isSharedCheck_1665_ = (!leanh::lean_is_exclusive(v___x_1646_)) as u8;
                    if v_isSharedCheck_1665_ == 0 {
                        v___x_1653_ = v___x_1646_;
                        v_isShared_1654_ = v_isSharedCheck_1665_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_err_1651_);
                        leanh::lean_inc(v_pos_1650_);
                        leanh::lean_dec(v___x_1646_);
                        v___x_1653_ = leanh::lean_box(0);
                        v_isShared_1654_ = v_isSharedCheck_1665_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v_pos_1655_ = leanh::lean_ctor_get(v_inst_1640_, 0);
                leanh::lean_inc_n(v_pos_1655_, 2);
                leanh::lean_dec_ref(v_inst_1640_);
                v___x_1656_ = leanh::lean_apply_1(v_pos_1655_, v_it_1645_);
                leanh::lean_inc(v_pos_1650_);
                v___x_1657_ = leanh::lean_apply_1(v_pos_1655_, v_pos_1650_);
                v___x_1658_ = leanh::lean_apply_2(v_inst_1638_, v___x_1656_, v___x_1657_);
                v___x_1659_ = (leanh::lean_unbox(v___x_1658_) as u8);
                if v___x_1659_ == 0 {
                    leanh::lean_dec_ref(v_cerror_1644_);
                    if v_isShared_1654_ == 0 {
                        v___x_1661_ = v___x_1653_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_1662_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_1662_, 0, v_pos_1650_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_1662_, 1, v_err_1651_);
                        v___x_1661_ = v_reuseFailAlloc_1662_;
                        state = 2;
                        continue;
                    }
                } else {
                    leanh::lean_del_object(v___x_1653_);
                    leanh::lean_dec(v_err_1651_);
                    v___x_1663_ = leanh::lean_box(0);
                    v___x_1664_ =
                        leanh::lean_apply_2(v_cerror_1644_, v___x_1663_, v_pos_1650_);
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
    mut v_00_u03b1_1666_: *mut leanh::LeanObject,
    mut v_00_u03b9_1667_: *mut leanh::LeanObject,
    mut v_elem_1668_: *mut leanh::LeanObject,
    mut v_idx_1669_: *mut leanh::LeanObject,
    mut v_inst_1670_: *mut leanh::LeanObject,
    mut v_inst_1671_: *mut leanh::LeanObject,
    mut v_inst_1672_: *mut leanh::LeanObject,
    mut v_00_u03b2_1673_: *mut leanh::LeanObject,
    mut v_p_1674_: *mut leanh::LeanObject,
    mut v_csuccess_1675_: *mut leanh::LeanObject,
    mut v_cerror_1676_: *mut leanh::LeanObject,
    mut v_it_1677_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1678_: *mut leanh::LeanObject = core::ptr::null_mut();
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
    leanh::lean_dec_ref(v_inst_1671_);
    return v_res_1678_;
}
pub unsafe fn l_Std_Internal_Parsec_instMonad___lam__0(
    mut v_00_u03b1_1679_: *mut leanh::LeanObject,
    mut v_00_u03b2_1680_: *mut leanh::LeanObject,
    mut v_f_1681_: *mut leanh::LeanObject,
    mut v_x_1682_: *mut leanh::LeanObject,
    mut v___y_1683_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1684_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_pos_1685_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_res_1686_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1688_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1689_: u8 = 0;
    let mut v___x_1690_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1692_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1693_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1694_: u8 = 0;
    let mut v_pos_1695_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_err_1696_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1698_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1699_: u8 = 0;
    let mut v___x_1701_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1702_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1703_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1684_ = leanh::lean_apply_1(v_x_1682_, v___y_1683_);
                if leanh::lean_obj_tag(v___x_1684_) == 0 {
                    v_pos_1685_ = leanh::lean_ctor_get(v___x_1684_, 0);
                    v_res_1686_ = leanh::lean_ctor_get(v___x_1684_, 1);
                    v_isSharedCheck_1694_ = (!leanh::lean_is_exclusive(v___x_1684_)) as u8;
                    if v_isSharedCheck_1694_ == 0 {
                        v___x_1688_ = v___x_1684_;
                        v_isShared_1689_ = v_isSharedCheck_1694_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_res_1686_);
                        leanh::lean_inc(v_pos_1685_);
                        leanh::lean_dec(v___x_1684_);
                        v___x_1688_ = leanh::lean_box(0);
                        v_isShared_1689_ = v_isSharedCheck_1694_;
                        state = 1;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v_f_1681_);
                    v_pos_1695_ = leanh::lean_ctor_get(v___x_1684_, 0);
                    v_err_1696_ = leanh::lean_ctor_get(v___x_1684_, 1);
                    v_isSharedCheck_1703_ = (!leanh::lean_is_exclusive(v___x_1684_)) as u8;
                    if v_isSharedCheck_1703_ == 0 {
                        v___x_1698_ = v___x_1684_;
                        v_isShared_1699_ = v_isSharedCheck_1703_;
                        state = 3;
                        continue;
                    } else {
                        leanh::lean_inc(v_err_1696_);
                        leanh::lean_inc(v_pos_1695_);
                        leanh::lean_dec(v___x_1684_);
                        v___x_1698_ = leanh::lean_box(0);
                        v_isShared_1699_ = v_isSharedCheck_1703_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v___x_1690_ = leanh::lean_apply_1(v_f_1681_, v_res_1686_);
                if v_isShared_1689_ == 0 {
                    leanh::lean_ctor_set(v___x_1688_, 1, v___x_1690_);
                    v___x_1692_ = v___x_1688_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1693_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1693_, 0, v_pos_1685_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1693_, 1, v___x_1690_);
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
                    v_reuseFailAlloc_1702_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1702_, 0, v_pos_1695_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1702_, 1, v_err_1696_);
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
    mut v_00_u03b1_1704_: *mut leanh::LeanObject,
    mut v_00_u03b2_1705_: *mut leanh::LeanObject,
    mut v___y_1706_: *mut leanh::LeanObject,
    mut v___y_1707_: *mut leanh::LeanObject,
    mut v___y_1708_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1709_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_pos_1710_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1712_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1713_: u8 = 0;
    let mut v___x_1715_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1716_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1717_: u8 = 0;
    let mut v_unused_1718_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_pos_1719_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_err_1720_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1722_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1723_: u8 = 0;
    let mut v___x_1725_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1726_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1727_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1709_ = leanh::lean_apply_1(v___y_1707_, v___y_1708_);
                if leanh::lean_obj_tag(v___x_1709_) == 0 {
                    v_pos_1710_ = leanh::lean_ctor_get(v___x_1709_, 0);
                    v_isSharedCheck_1717_ = (!leanh::lean_is_exclusive(v___x_1709_)) as u8;
                    if v_isSharedCheck_1717_ == 0 {
                        v_unused_1718_ = leanh::lean_ctor_get(v___x_1709_, 1);
                        leanh::lean_dec(v_unused_1718_);
                        v___x_1712_ = v___x_1709_;
                        v_isShared_1713_ = v_isSharedCheck_1717_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_pos_1710_);
                        leanh::lean_dec(v___x_1709_);
                        v___x_1712_ = leanh::lean_box(0);
                        v_isShared_1713_ = v_isSharedCheck_1717_;
                        state = 1;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v___y_1706_);
                    v_pos_1719_ = leanh::lean_ctor_get(v___x_1709_, 0);
                    v_err_1720_ = leanh::lean_ctor_get(v___x_1709_, 1);
                    v_isSharedCheck_1727_ = (!leanh::lean_is_exclusive(v___x_1709_)) as u8;
                    if v_isSharedCheck_1727_ == 0 {
                        v___x_1722_ = v___x_1709_;
                        v_isShared_1723_ = v_isSharedCheck_1727_;
                        state = 3;
                        continue;
                    } else {
                        leanh::lean_inc(v_err_1720_);
                        leanh::lean_inc(v_pos_1719_);
                        leanh::lean_dec(v___x_1709_);
                        v___x_1722_ = leanh::lean_box(0);
                        v_isShared_1723_ = v_isSharedCheck_1727_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_1713_ == 0 {
                    leanh::lean_ctor_set(v___x_1712_, 1, v___y_1706_);
                    v___x_1715_ = v___x_1712_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1716_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1716_, 0, v_pos_1710_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1716_, 1, v___y_1706_);
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
                    v_reuseFailAlloc_1726_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1726_, 0, v_pos_1719_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1726_, 1, v_err_1720_);
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
    mut v_00_u03b1_1728_: *mut leanh::LeanObject,
    mut v___y_1729_: *mut leanh::LeanObject,
    mut v___y_1730_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1731_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1731_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_1731_, 0, v___y_1730_);
    leanh::lean_ctor_set(v___x_1731_, 1, v___y_1729_);
    return v___x_1731_;
}
pub unsafe fn l_Std_Internal_Parsec_instMonad___lam__3(
    mut v_00_u03b1_1732_: *mut leanh::LeanObject,
    mut v_00_u03b2_1733_: *mut leanh::LeanObject,
    mut v_f_1734_: *mut leanh::LeanObject,
    mut v_x_1735_: *mut leanh::LeanObject,
    mut v___y_1736_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1737_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_pos_1738_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_res_1739_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1740_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1741_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_pos_1742_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_res_1743_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1745_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1746_: u8 = 0;
    let mut v___x_1747_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1749_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1750_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1751_: u8 = 0;
    let mut v_pos_1752_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_err_1753_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1755_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1756_: u8 = 0;
    let mut v___x_1758_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1759_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1760_: u8 = 0;
    let mut v_pos_1761_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_err_1762_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1764_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1765_: u8 = 0;
    let mut v___x_1767_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1768_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1769_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1737_ = leanh::lean_apply_1(v_f_1734_, v___y_1736_);
                if leanh::lean_obj_tag(v___x_1737_) == 0 {
                    v_pos_1738_ = leanh::lean_ctor_get(v___x_1737_, 0);
                    leanh::lean_inc(v_pos_1738_);
                    v_res_1739_ = leanh::lean_ctor_get(v___x_1737_, 1);
                    leanh::lean_inc(v_res_1739_);
                    leanh::lean_dec_ref_known(v___x_1737_, 2);
                    v___x_1740_ = leanh::lean_box(0);
                    v___x_1741_ = leanh::lean_apply_2(v_x_1735_, v___x_1740_, v_pos_1738_);
                    if leanh::lean_obj_tag(v___x_1741_) == 0 {
                        v_pos_1742_ = leanh::lean_ctor_get(v___x_1741_, 0);
                        v_res_1743_ = leanh::lean_ctor_get(v___x_1741_, 1);
                        v_isSharedCheck_1751_ =
                            (!leanh::lean_is_exclusive(v___x_1741_)) as u8;
                        if v_isSharedCheck_1751_ == 0 {
                            v___x_1745_ = v___x_1741_;
                            v_isShared_1746_ = v_isSharedCheck_1751_;
                            state = 1;
                            continue;
                        } else {
                            leanh::lean_inc(v_res_1743_);
                            leanh::lean_inc(v_pos_1742_);
                            leanh::lean_dec(v___x_1741_);
                            v___x_1745_ = leanh::lean_box(0);
                            v_isShared_1746_ = v_isSharedCheck_1751_;
                            state = 1;
                            continue;
                        }
                    } else {
                        leanh::lean_dec(v_res_1739_);
                        v_pos_1752_ = leanh::lean_ctor_get(v___x_1741_, 0);
                        v_err_1753_ = leanh::lean_ctor_get(v___x_1741_, 1);
                        v_isSharedCheck_1760_ =
                            (!leanh::lean_is_exclusive(v___x_1741_)) as u8;
                        if v_isSharedCheck_1760_ == 0 {
                            v___x_1755_ = v___x_1741_;
                            v_isShared_1756_ = v_isSharedCheck_1760_;
                            state = 3;
                            continue;
                        } else {
                            leanh::lean_inc(v_err_1753_);
                            leanh::lean_inc(v_pos_1752_);
                            leanh::lean_dec(v___x_1741_);
                            v___x_1755_ = leanh::lean_box(0);
                            v_isShared_1756_ = v_isSharedCheck_1760_;
                            state = 3;
                            continue;
                        }
                    }
                } else {
                    leanh::lean_dec_ref(v_x_1735_);
                    v_pos_1761_ = leanh::lean_ctor_get(v___x_1737_, 0);
                    v_err_1762_ = leanh::lean_ctor_get(v___x_1737_, 1);
                    v_isSharedCheck_1769_ = (!leanh::lean_is_exclusive(v___x_1737_)) as u8;
                    if v_isSharedCheck_1769_ == 0 {
                        v___x_1764_ = v___x_1737_;
                        v_isShared_1765_ = v_isSharedCheck_1769_;
                        state = 5;
                        continue;
                    } else {
                        leanh::lean_inc(v_err_1762_);
                        leanh::lean_inc(v_pos_1761_);
                        leanh::lean_dec(v___x_1737_);
                        v___x_1764_ = leanh::lean_box(0);
                        v_isShared_1765_ = v_isSharedCheck_1769_;
                        state = 5;
                        continue;
                    }
                }
            }
            1 => {
                v___x_1747_ = leanh::lean_apply_1(v_res_1739_, v_res_1743_);
                if v_isShared_1746_ == 0 {
                    leanh::lean_ctor_set(v___x_1745_, 1, v___x_1747_);
                    v___x_1749_ = v___x_1745_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1750_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1750_, 0, v_pos_1742_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1750_, 1, v___x_1747_);
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
                    v_reuseFailAlloc_1759_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1759_, 0, v_pos_1752_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1759_, 1, v_err_1753_);
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
                    v_reuseFailAlloc_1768_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1768_, 0, v_pos_1761_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1768_, 1, v_err_1762_);
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
    mut v_00_u03b1_1770_: *mut leanh::LeanObject,
    mut v_00_u03b2_1771_: *mut leanh::LeanObject,
    mut v_x_1772_: *mut leanh::LeanObject,
    mut v_y_1773_: *mut leanh::LeanObject,
    mut v___y_1774_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1775_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_pos_1776_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_res_1777_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1778_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1779_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_pos_1780_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1782_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1783_: u8 = 0;
    let mut v___x_1785_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1786_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1787_: u8 = 0;
    let mut v_unused_1788_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_pos_1789_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_err_1790_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1792_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1793_: u8 = 0;
    let mut v___x_1795_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1796_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1797_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1775_ = leanh::lean_apply_1(v_x_1772_, v___y_1774_);
                if leanh::lean_obj_tag(v___x_1775_) == 0 {
                    v_pos_1776_ = leanh::lean_ctor_get(v___x_1775_, 0);
                    leanh::lean_inc(v_pos_1776_);
                    v_res_1777_ = leanh::lean_ctor_get(v___x_1775_, 1);
                    leanh::lean_inc(v_res_1777_);
                    leanh::lean_dec_ref_known(v___x_1775_, 2);
                    v___x_1778_ = leanh::lean_box(0);
                    v___x_1779_ = leanh::lean_apply_2(v_y_1773_, v___x_1778_, v_pos_1776_);
                    if leanh::lean_obj_tag(v___x_1779_) == 0 {
                        v_pos_1780_ = leanh::lean_ctor_get(v___x_1779_, 0);
                        v_isSharedCheck_1787_ =
                            (!leanh::lean_is_exclusive(v___x_1779_)) as u8;
                        if v_isSharedCheck_1787_ == 0 {
                            v_unused_1788_ = leanh::lean_ctor_get(v___x_1779_, 1);
                            leanh::lean_dec(v_unused_1788_);
                            v___x_1782_ = v___x_1779_;
                            v_isShared_1783_ = v_isSharedCheck_1787_;
                            state = 1;
                            continue;
                        } else {
                            leanh::lean_inc(v_pos_1780_);
                            leanh::lean_dec(v___x_1779_);
                            v___x_1782_ = leanh::lean_box(0);
                            v_isShared_1783_ = v_isSharedCheck_1787_;
                            state = 1;
                            continue;
                        }
                    } else {
                        leanh::lean_dec(v_res_1777_);
                        v_pos_1789_ = leanh::lean_ctor_get(v___x_1779_, 0);
                        v_err_1790_ = leanh::lean_ctor_get(v___x_1779_, 1);
                        v_isSharedCheck_1797_ =
                            (!leanh::lean_is_exclusive(v___x_1779_)) as u8;
                        if v_isSharedCheck_1797_ == 0 {
                            v___x_1792_ = v___x_1779_;
                            v_isShared_1793_ = v_isSharedCheck_1797_;
                            state = 3;
                            continue;
                        } else {
                            leanh::lean_inc(v_err_1790_);
                            leanh::lean_inc(v_pos_1789_);
                            leanh::lean_dec(v___x_1779_);
                            v___x_1792_ = leanh::lean_box(0);
                            v_isShared_1793_ = v_isSharedCheck_1797_;
                            state = 3;
                            continue;
                        }
                    }
                } else {
                    leanh::lean_dec_ref(v_y_1773_);
                    return v___x_1775_;
                }
            }
            1 => {
                if v_isShared_1783_ == 0 {
                    leanh::lean_ctor_set(v___x_1782_, 1, v_res_1777_);
                    v___x_1785_ = v___x_1782_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1786_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1786_, 0, v_pos_1780_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1786_, 1, v_res_1777_);
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
                    v_reuseFailAlloc_1796_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1796_, 0, v_pos_1789_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1796_, 1, v_err_1790_);
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
    mut v_00_u03b1_1798_: *mut leanh::LeanObject,
    mut v_00_u03b2_1799_: *mut leanh::LeanObject,
    mut v_x_1800_: *mut leanh::LeanObject,
    mut v_y_1801_: *mut leanh::LeanObject,
    mut v___y_1802_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1803_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_pos_1804_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1805_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1806_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_pos_1807_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_err_1808_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1810_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1811_: u8 = 0;
    let mut v___x_1813_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1814_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1815_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1803_ = leanh::lean_apply_1(v_x_1800_, v___y_1802_);
                if leanh::lean_obj_tag(v___x_1803_) == 0 {
                    v_pos_1804_ = leanh::lean_ctor_get(v___x_1803_, 0);
                    leanh::lean_inc(v_pos_1804_);
                    leanh::lean_dec_ref_known(v___x_1803_, 2);
                    v___x_1805_ = leanh::lean_box(0);
                    v___x_1806_ = leanh::lean_apply_2(v_y_1801_, v___x_1805_, v_pos_1804_);
                    return v___x_1806_;
                } else {
                    leanh::lean_dec_ref(v_y_1801_);
                    v_pos_1807_ = leanh::lean_ctor_get(v___x_1803_, 0);
                    v_err_1808_ = leanh::lean_ctor_get(v___x_1803_, 1);
                    v_isSharedCheck_1815_ = (!leanh::lean_is_exclusive(v___x_1803_)) as u8;
                    if v_isSharedCheck_1815_ == 0 {
                        v___x_1810_ = v___x_1803_;
                        v_isShared_1811_ = v_isSharedCheck_1815_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_err_1808_);
                        leanh::lean_inc(v_pos_1807_);
                        leanh::lean_dec(v___x_1803_);
                        v___x_1810_ = leanh::lean_box(0);
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
                    v_reuseFailAlloc_1814_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1814_, 0, v_pos_1807_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1814_, 1, v_err_1808_);
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
    mut v_00_u03b9_1835_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1836_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1836_ = l_Std_Internal_Parsec_instMonad___closed__9;
    return v___x_1836_;
}
pub unsafe fn l_Std_Internal_Parsec_orElse___redArg(
    mut v_inst_1837_: *mut leanh::LeanObject,
    mut v_inst_1838_: *mut leanh::LeanObject,
    mut v_p_1839_: *mut leanh::LeanObject,
    mut v_q_1840_: *mut leanh::LeanObject,
    mut v_a_1841_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1842_: *mut leanh::LeanObject = core::ptr::null_mut();
    leanh::lean_inc(v_a_1841_);
    v___x_1842_ = leanh::lean_apply_1(v_p_1839_, v_a_1841_);
    if leanh::lean_obj_tag(v___x_1842_) == 0 {
        leanh::lean_dec(v_a_1841_);
        leanh::lean_dec_ref(v_q_1840_);
        leanh::lean_dec_ref(v_inst_1838_);
        leanh::lean_dec_ref(v_inst_1837_);
        return v___x_1842_;
    } else {
        let mut v_pos_1843_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_pos_1844_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1845_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1846_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1847_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1848_: u8 = 0;
        v_pos_1843_ = leanh::lean_ctor_get(v___x_1842_, 0);
        leanh::lean_inc_n(v_pos_1843_, 2);
        v_pos_1844_ = leanh::lean_ctor_get(v_inst_1838_, 0);
        leanh::lean_inc_n(v_pos_1844_, 2);
        leanh::lean_dec_ref(v_inst_1838_);
        v___x_1845_ = leanh::lean_apply_1(v_pos_1844_, v_a_1841_);
        v___x_1846_ = leanh::lean_apply_1(v_pos_1844_, v_pos_1843_);
        v___x_1847_ = leanh::lean_apply_2(v_inst_1837_, v___x_1845_, v___x_1846_);
        v___x_1848_ = (leanh::lean_unbox(v___x_1847_) as u8);
        if v___x_1848_ == 0 {
            leanh::lean_dec(v_pos_1843_);
            leanh::lean_dec_ref(v_q_1840_);
            return v___x_1842_;
        } else {
            let mut v___x_1849_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1850_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec_ref_known(v___x_1842_, 2);
            v___x_1849_ = leanh::lean_box(0);
            v___x_1850_ = leanh::lean_apply_2(v_q_1840_, v___x_1849_, v_pos_1843_);
            return v___x_1850_;
        }
    }
}
pub unsafe fn l_Std_Internal_Parsec_orElse(
    mut v_00_u03b1_1851_: *mut leanh::LeanObject,
    mut v_00_u03b9_1852_: *mut leanh::LeanObject,
    mut v_elem_1853_: *mut leanh::LeanObject,
    mut v_idx_1854_: *mut leanh::LeanObject,
    mut v_inst_1855_: *mut leanh::LeanObject,
    mut v_inst_1856_: *mut leanh::LeanObject,
    mut v_inst_1857_: *mut leanh::LeanObject,
    mut v_p_1858_: *mut leanh::LeanObject,
    mut v_q_1859_: *mut leanh::LeanObject,
    mut v_a_1860_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1861_: *mut leanh::LeanObject = core::ptr::null_mut();
    leanh::lean_inc(v_a_1860_);
    v___x_1861_ = leanh::lean_apply_1(v_p_1858_, v_a_1860_);
    if leanh::lean_obj_tag(v___x_1861_) == 0 {
        leanh::lean_dec(v_a_1860_);
        leanh::lean_dec_ref(v_q_1859_);
        leanh::lean_dec_ref(v_inst_1857_);
        leanh::lean_dec_ref(v_inst_1855_);
        return v___x_1861_;
    } else {
        let mut v_pos_1862_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_pos_1863_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1864_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1865_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1866_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1867_: u8 = 0;
        v_pos_1862_ = leanh::lean_ctor_get(v___x_1861_, 0);
        leanh::lean_inc_n(v_pos_1862_, 2);
        v_pos_1863_ = leanh::lean_ctor_get(v_inst_1857_, 0);
        leanh::lean_inc_n(v_pos_1863_, 2);
        leanh::lean_dec_ref(v_inst_1857_);
        v___x_1864_ = leanh::lean_apply_1(v_pos_1863_, v_a_1860_);
        v___x_1865_ = leanh::lean_apply_1(v_pos_1863_, v_pos_1862_);
        v___x_1866_ = leanh::lean_apply_2(v_inst_1855_, v___x_1864_, v___x_1865_);
        v___x_1867_ = (leanh::lean_unbox(v___x_1866_) as u8);
        if v___x_1867_ == 0 {
            leanh::lean_dec(v_pos_1862_);
            leanh::lean_dec_ref(v_q_1859_);
            return v___x_1861_;
        } else {
            let mut v___x_1868_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1869_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec_ref_known(v___x_1861_, 2);
            v___x_1868_ = leanh::lean_box(0);
            v___x_1869_ = leanh::lean_apply_2(v_q_1859_, v___x_1868_, v_pos_1862_);
            return v___x_1869_;
        }
    }
}
pub unsafe fn l_Std_Internal_Parsec_orElse___boxed(
    mut v_00_u03b1_1870_: *mut leanh::LeanObject,
    mut v_00_u03b9_1871_: *mut leanh::LeanObject,
    mut v_elem_1872_: *mut leanh::LeanObject,
    mut v_idx_1873_: *mut leanh::LeanObject,
    mut v_inst_1874_: *mut leanh::LeanObject,
    mut v_inst_1875_: *mut leanh::LeanObject,
    mut v_inst_1876_: *mut leanh::LeanObject,
    mut v_p_1877_: *mut leanh::LeanObject,
    mut v_q_1878_: *mut leanh::LeanObject,
    mut v_a_1879_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1880_: *mut leanh::LeanObject = core::ptr::null_mut();
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
    leanh::lean_dec_ref(v_inst_1875_);
    return v_res_1880_;
}
pub unsafe fn l_Std_Internal_Parsec_attempt___redArg(
    mut v_p_1881_: *mut leanh::LeanObject,
    mut v_it_1882_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1883_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_err_1884_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1886_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1887_: u8 = 0;
    let mut v___x_1889_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1890_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1891_: u8 = 0;
    let mut v_unused_1892_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                leanh::lean_inc(v_it_1882_);
                v___x_1883_ = leanh::lean_apply_1(v_p_1881_, v_it_1882_);
                if leanh::lean_obj_tag(v___x_1883_) == 0 {
                    leanh::lean_dec(v_it_1882_);
                    return v___x_1883_;
                } else {
                    v_err_1884_ = leanh::lean_ctor_get(v___x_1883_, 1);
                    v_isSharedCheck_1891_ = (!leanh::lean_is_exclusive(v___x_1883_)) as u8;
                    if v_isSharedCheck_1891_ == 0 {
                        v_unused_1892_ = leanh::lean_ctor_get(v___x_1883_, 0);
                        leanh::lean_dec(v_unused_1892_);
                        v___x_1886_ = v___x_1883_;
                        v_isShared_1887_ = v_isSharedCheck_1891_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_err_1884_);
                        leanh::lean_dec(v___x_1883_);
                        v___x_1886_ = leanh::lean_box(0);
                        v_isShared_1887_ = v_isSharedCheck_1891_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_1887_ == 0 {
                    leanh::lean_ctor_set(v___x_1886_, 0, v_it_1882_);
                    v___x_1889_ = v___x_1886_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1890_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1890_, 0, v_it_1882_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1890_, 1, v_err_1884_);
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
    mut v_00_u03b1_1893_: *mut leanh::LeanObject,
    mut v_00_u03b9_1894_: *mut leanh::LeanObject,
    mut v_p_1895_: *mut leanh::LeanObject,
    mut v_it_1896_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1897_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_err_1898_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1900_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1901_: u8 = 0;
    let mut v___x_1903_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1904_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1905_: u8 = 0;
    let mut v_unused_1906_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                leanh::lean_inc(v_it_1896_);
                v___x_1897_ = leanh::lean_apply_1(v_p_1895_, v_it_1896_);
                if leanh::lean_obj_tag(v___x_1897_) == 0 {
                    leanh::lean_dec(v_it_1896_);
                    return v___x_1897_;
                } else {
                    v_err_1898_ = leanh::lean_ctor_get(v___x_1897_, 1);
                    v_isSharedCheck_1905_ = (!leanh::lean_is_exclusive(v___x_1897_)) as u8;
                    if v_isSharedCheck_1905_ == 0 {
                        v_unused_1906_ = leanh::lean_ctor_get(v___x_1897_, 0);
                        leanh::lean_dec(v_unused_1906_);
                        v___x_1900_ = v___x_1897_;
                        v_isShared_1901_ = v_isSharedCheck_1905_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_err_1898_);
                        leanh::lean_dec(v___x_1897_);
                        v___x_1900_ = leanh::lean_box(0);
                        v_isShared_1901_ = v_isSharedCheck_1905_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_1901_ == 0 {
                    leanh::lean_ctor_set(v___x_1900_, 0, v_it_1896_);
                    v___x_1903_ = v___x_1900_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1904_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1904_, 0, v_it_1896_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1904_, 1, v_err_1898_);
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
    mut v_00_u03b1_1907_: *mut leanh::LeanObject,
    mut v___y_1908_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1909_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1910_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1909_ = l_Std_Internal_Parsec_instInhabited___lam__0___closed__1;
    v___x_1910_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_1910_, 0, v___y_1908_);
    leanh::lean_ctor_set(v___x_1910_, 1, v___x_1909_);
    return v___x_1910_;
}
pub unsafe fn l_Std_Internal_Parsec_instAlternative___redArg___lam__1(
    mut v_inst_1911_: *mut leanh::LeanObject,
    mut v_inst_1912_: *mut leanh::LeanObject,
    mut v_00_u03b1_1913_: *mut leanh::LeanObject,
    mut v___y_1914_: *mut leanh::LeanObject,
    mut v___y_1915_: *mut leanh::LeanObject,
    mut v___y_1916_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1917_: *mut leanh::LeanObject = core::ptr::null_mut();
    leanh::lean_inc(v___y_1916_);
    v___x_1917_ = leanh::lean_apply_1(v___y_1914_, v___y_1916_);
    if leanh::lean_obj_tag(v___x_1917_) == 0 {
        leanh::lean_dec(v___y_1916_);
        leanh::lean_dec_ref(v___y_1915_);
        leanh::lean_dec_ref(v_inst_1912_);
        leanh::lean_dec_ref(v_inst_1911_);
        return v___x_1917_;
    } else {
        let mut v_pos_1918_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_pos_1919_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1920_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1921_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1922_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1923_: u8 = 0;
        v_pos_1918_ = leanh::lean_ctor_get(v___x_1917_, 0);
        leanh::lean_inc_n(v_pos_1918_, 2);
        v_pos_1919_ = leanh::lean_ctor_get(v_inst_1911_, 0);
        leanh::lean_inc_n(v_pos_1919_, 2);
        leanh::lean_dec_ref(v_inst_1911_);
        v___x_1920_ = leanh::lean_apply_1(v_pos_1919_, v___y_1916_);
        v___x_1921_ = leanh::lean_apply_1(v_pos_1919_, v_pos_1918_);
        v___x_1922_ = leanh::lean_apply_2(v_inst_1912_, v___x_1920_, v___x_1921_);
        v___x_1923_ = (leanh::lean_unbox(v___x_1922_) as u8);
        if v___x_1923_ == 0 {
            leanh::lean_dec(v_pos_1918_);
            leanh::lean_dec_ref(v___y_1915_);
            return v___x_1917_;
        } else {
            let mut v___x_1924_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1925_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec_ref_known(v___x_1917_, 2);
            v___x_1924_ = leanh::lean_box(0);
            v___x_1925_ = leanh::lean_apply_2(v___y_1915_, v___x_1924_, v_pos_1918_);
            return v___x_1925_;
        }
    }
}
pub unsafe fn l_Std_Internal_Parsec_instAlternative___redArg(
    mut v_inst_1927_: *mut leanh::LeanObject,
    mut v_inst_1928_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_1929_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1930_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1931_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1932_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_1929_ = l_Std_Internal_Parsec_instAlternative___redArg___closed__0;
    v___f_1930_ = leanh::lean_alloc_closure(
        l_Std_Internal_Parsec_instAlternative___redArg___lam__1 as *mut core::ffi::c_void,
        6,
        2,
    );
    leanh::lean_closure_set(v___f_1930_, 0, v_inst_1928_);
    leanh::lean_closure_set(v___f_1930_, 1, v_inst_1927_);
    v___x_1931_ = l_Std_Internal_Parsec_instMonad___closed__7;
    v___x_1932_ = leanh::lean_alloc_ctor(0, 3, (0) as u32);
    leanh::lean_ctor_set(v___x_1932_, 0, v___x_1931_);
    leanh::lean_ctor_set(v___x_1932_, 1, v___f_1929_);
    leanh::lean_ctor_set(v___x_1932_, 2, v___f_1930_);
    return v___x_1932_;
}
pub unsafe fn l_Std_Internal_Parsec_instAlternative(
    mut v_00_u03b9_1933_: *mut leanh::LeanObject,
    mut v_elem_1934_: *mut leanh::LeanObject,
    mut v_idx_1935_: *mut leanh::LeanObject,
    mut v_inst_1936_: *mut leanh::LeanObject,
    mut v_inst_1937_: *mut leanh::LeanObject,
    mut v_inst_1938_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_1939_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1940_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1941_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1942_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_1939_ = l_Std_Internal_Parsec_instAlternative___redArg___closed__0;
    v___f_1940_ = leanh::lean_alloc_closure(
        l_Std_Internal_Parsec_instAlternative___redArg___lam__1 as *mut core::ffi::c_void,
        6,
        2,
    );
    leanh::lean_closure_set(v___f_1940_, 0, v_inst_1938_);
    leanh::lean_closure_set(v___f_1940_, 1, v_inst_1936_);
    v___x_1941_ = l_Std_Internal_Parsec_instMonad___closed__7;
    v___x_1942_ = leanh::lean_alloc_ctor(0, 3, (0) as u32);
    leanh::lean_ctor_set(v___x_1942_, 0, v___x_1941_);
    leanh::lean_ctor_set(v___x_1942_, 1, v___f_1939_);
    leanh::lean_ctor_set(v___x_1942_, 2, v___f_1940_);
    return v___x_1942_;
}
pub unsafe fn l_Std_Internal_Parsec_instAlternative___boxed(
    mut v_00_u03b9_1943_: *mut leanh::LeanObject,
    mut v_elem_1944_: *mut leanh::LeanObject,
    mut v_idx_1945_: *mut leanh::LeanObject,
    mut v_inst_1946_: *mut leanh::LeanObject,
    mut v_inst_1947_: *mut leanh::LeanObject,
    mut v_inst_1948_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1949_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1949_ = l_Std_Internal_Parsec_instAlternative(
        v_00_u03b9_1943_,
        v_elem_1944_,
        v_idx_1945_,
        v_inst_1946_,
        v_inst_1947_,
        v_inst_1948_,
    );
    leanh::lean_dec_ref(v_inst_1947_);
    return v_res_1949_;
}
pub unsafe fn l_Std_Internal_Parsec_eof___redArg(
    mut v_inst_1953_: *mut leanh::LeanObject,
    mut v_it_1954_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_hasNext_1955_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1956_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1957_: u8 = 0;
    v_hasNext_1955_ = leanh::lean_ctor_get(v_inst_1953_, 3);
    leanh::lean_inc_ref(v_hasNext_1955_);
    leanh::lean_dec_ref(v_inst_1953_);
    leanh::lean_inc(v_it_1954_);
    v___x_1956_ = leanh::lean_apply_1(v_hasNext_1955_, v_it_1954_);
    v___x_1957_ = (leanh::lean_unbox(v___x_1956_) as u8);
    if v___x_1957_ == 0 {
        let mut v___x_1958_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1959_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_1958_ = leanh::lean_box(0);
        v___x_1959_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
        leanh::lean_ctor_set(v___x_1959_, 0, v_it_1954_);
        leanh::lean_ctor_set(v___x_1959_, 1, v___x_1958_);
        return v___x_1959_;
    } else {
        let mut v___x_1960_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1961_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_1960_ = l_Std_Internal_Parsec_eof___redArg___closed__1;
        v___x_1961_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
        leanh::lean_ctor_set(v___x_1961_, 0, v_it_1954_);
        leanh::lean_ctor_set(v___x_1961_, 1, v___x_1960_);
        return v___x_1961_;
    }
}
pub unsafe fn l_Std_Internal_Parsec_eof(
    mut v_00_u03b9_1962_: *mut leanh::LeanObject,
    mut v_elem_1963_: *mut leanh::LeanObject,
    mut v_idx_1964_: *mut leanh::LeanObject,
    mut v_inst_1965_: *mut leanh::LeanObject,
    mut v_inst_1966_: *mut leanh::LeanObject,
    mut v_inst_1967_: *mut leanh::LeanObject,
    mut v_it_1968_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_hasNext_1969_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1970_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1971_: u8 = 0;
    v_hasNext_1969_ = leanh::lean_ctor_get(v_inst_1967_, 3);
    leanh::lean_inc_ref(v_hasNext_1969_);
    leanh::lean_dec_ref(v_inst_1967_);
    leanh::lean_inc(v_it_1968_);
    v___x_1970_ = leanh::lean_apply_1(v_hasNext_1969_, v_it_1968_);
    v___x_1971_ = (leanh::lean_unbox(v___x_1970_) as u8);
    if v___x_1971_ == 0 {
        let mut v___x_1972_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1973_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_1972_ = leanh::lean_box(0);
        v___x_1973_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
        leanh::lean_ctor_set(v___x_1973_, 0, v_it_1968_);
        leanh::lean_ctor_set(v___x_1973_, 1, v___x_1972_);
        return v___x_1973_;
    } else {
        let mut v___x_1974_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1975_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_1974_ = l_Std_Internal_Parsec_eof___redArg___closed__1;
        v___x_1975_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
        leanh::lean_ctor_set(v___x_1975_, 0, v_it_1968_);
        leanh::lean_ctor_set(v___x_1975_, 1, v___x_1974_);
        return v___x_1975_;
    }
}
pub unsafe fn l_Std_Internal_Parsec_eof___boxed(
    mut v_00_u03b9_1976_: *mut leanh::LeanObject,
    mut v_elem_1977_: *mut leanh::LeanObject,
    mut v_idx_1978_: *mut leanh::LeanObject,
    mut v_inst_1979_: *mut leanh::LeanObject,
    mut v_inst_1980_: *mut leanh::LeanObject,
    mut v_inst_1981_: *mut leanh::LeanObject,
    mut v_it_1982_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1983_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1983_ = l_Std_Internal_Parsec_eof(
        v_00_u03b9_1976_,
        v_elem_1977_,
        v_idx_1978_,
        v_inst_1979_,
        v_inst_1980_,
        v_inst_1981_,
        v_it_1982_,
    );
    leanh::lean_dec_ref(v_inst_1980_);
    leanh::lean_dec_ref(v_inst_1979_);
    return v_res_1983_;
}
pub unsafe fn l_Std_Internal_Parsec_isEof___redArg(
    mut v_inst_1984_: *mut leanh::LeanObject,
    mut v_it_1985_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_hasNext_1986_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1987_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1988_: u8 = 0;
    v_hasNext_1986_ = leanh::lean_ctor_get(v_inst_1984_, 3);
    leanh::lean_inc_ref(v_hasNext_1986_);
    leanh::lean_dec_ref(v_inst_1984_);
    leanh::lean_inc(v_it_1985_);
    v___x_1987_ = leanh::lean_apply_1(v_hasNext_1986_, v_it_1985_);
    v___x_1988_ = (leanh::lean_unbox(v___x_1987_) as u8);
    if v___x_1988_ == 0 {
        let mut v___x_1989_: u8 = 0;
        let mut v___x_1990_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1991_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_1989_ = 1;
        v___x_1990_ = leanh::lean_box((v___x_1989_) as usize);
        v___x_1991_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
        leanh::lean_ctor_set(v___x_1991_, 0, v_it_1985_);
        leanh::lean_ctor_set(v___x_1991_, 1, v___x_1990_);
        return v___x_1991_;
    } else {
        let mut v___x_1992_: u8 = 0;
        let mut v___x_1993_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1994_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_1992_ = 0;
        v___x_1993_ = leanh::lean_box((v___x_1992_) as usize);
        v___x_1994_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
        leanh::lean_ctor_set(v___x_1994_, 0, v_it_1985_);
        leanh::lean_ctor_set(v___x_1994_, 1, v___x_1993_);
        return v___x_1994_;
    }
}
pub unsafe fn l_Std_Internal_Parsec_isEof(
    mut v_00_u03b9_1995_: *mut leanh::LeanObject,
    mut v_elem_1996_: *mut leanh::LeanObject,
    mut v_idx_1997_: *mut leanh::LeanObject,
    mut v_inst_1998_: *mut leanh::LeanObject,
    mut v_inst_1999_: *mut leanh::LeanObject,
    mut v_inst_2000_: *mut leanh::LeanObject,
    mut v_it_2001_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_hasNext_2002_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2003_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2004_: u8 = 0;
    v_hasNext_2002_ = leanh::lean_ctor_get(v_inst_2000_, 3);
    leanh::lean_inc_ref(v_hasNext_2002_);
    leanh::lean_dec_ref(v_inst_2000_);
    leanh::lean_inc(v_it_2001_);
    v___x_2003_ = leanh::lean_apply_1(v_hasNext_2002_, v_it_2001_);
    v___x_2004_ = (leanh::lean_unbox(v___x_2003_) as u8);
    if v___x_2004_ == 0 {
        let mut v___x_2005_: u8 = 0;
        let mut v___x_2006_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2007_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_2005_ = 1;
        v___x_2006_ = leanh::lean_box((v___x_2005_) as usize);
        v___x_2007_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
        leanh::lean_ctor_set(v___x_2007_, 0, v_it_2001_);
        leanh::lean_ctor_set(v___x_2007_, 1, v___x_2006_);
        return v___x_2007_;
    } else {
        let mut v___x_2008_: u8 = 0;
        let mut v___x_2009_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2010_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_2008_ = 0;
        v___x_2009_ = leanh::lean_box((v___x_2008_) as usize);
        v___x_2010_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
        leanh::lean_ctor_set(v___x_2010_, 0, v_it_2001_);
        leanh::lean_ctor_set(v___x_2010_, 1, v___x_2009_);
        return v___x_2010_;
    }
}
pub unsafe fn l_Std_Internal_Parsec_isEof___boxed(
    mut v_00_u03b9_2011_: *mut leanh::LeanObject,
    mut v_elem_2012_: *mut leanh::LeanObject,
    mut v_idx_2013_: *mut leanh::LeanObject,
    mut v_inst_2014_: *mut leanh::LeanObject,
    mut v_inst_2015_: *mut leanh::LeanObject,
    mut v_inst_2016_: *mut leanh::LeanObject,
    mut v_it_2017_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2018_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2018_ = l_Std_Internal_Parsec_isEof(
        v_00_u03b9_2011_,
        v_elem_2012_,
        v_idx_2013_,
        v_inst_2014_,
        v_inst_2015_,
        v_inst_2016_,
        v_it_2017_,
    );
    leanh::lean_dec_ref(v_inst_2015_);
    leanh::lean_dec_ref(v_inst_2014_);
    return v_res_2018_;
}
pub unsafe fn l_Std_Internal_Parsec_manyCore___redArg(
    mut v_inst_2019_: *mut leanh::LeanObject,
    mut v_inst_2020_: *mut leanh::LeanObject,
    mut v_p_2021_: *mut leanh::LeanObject,
    mut v_acc_2022_: *mut leanh::LeanObject,
    mut v_a_2023_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2024_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_pos_2025_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_res_2026_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2027_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_pos_2029_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_err_2030_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2032_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2033_: u8 = 0;
    let mut v_pos_2034_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2035_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2036_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2037_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2038_: u8 = 0;
    let mut v___x_2040_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2041_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2043_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2044_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2045_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                leanh::lean_inc_ref(v_p_2021_);
                leanh::lean_inc(v_a_2023_);
                v___x_2024_ = leanh::lean_apply_1(v_p_2021_, v_a_2023_);
                if leanh::lean_obj_tag(v___x_2024_) == 0 {
                    leanh::lean_dec(v_a_2023_);
                    v_pos_2025_ = leanh::lean_ctor_get(v___x_2024_, 0);
                    leanh::lean_inc(v_pos_2025_);
                    v_res_2026_ = leanh::lean_ctor_get(v___x_2024_, 1);
                    leanh::lean_inc(v_res_2026_);
                    leanh::lean_dec_ref_known(v___x_2024_, 2);
                    v___x_2027_ = lean_array_push(v_acc_2022_, v_res_2026_);
                    v_acc_2022_ = v___x_2027_;
                    v_a_2023_ = v_pos_2025_;
                    state = 0;
                    continue;
                } else {
                    leanh::lean_dec_ref(v_p_2021_);
                    v_pos_2029_ = leanh::lean_ctor_get(v___x_2024_, 0);
                    v_err_2030_ = leanh::lean_ctor_get(v___x_2024_, 1);
                    v_isSharedCheck_2045_ = (!leanh::lean_is_exclusive(v___x_2024_)) as u8;
                    if v_isSharedCheck_2045_ == 0 {
                        v___x_2032_ = v___x_2024_;
                        v_isShared_2033_ = v_isSharedCheck_2045_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_err_2030_);
                        leanh::lean_inc(v_pos_2029_);
                        leanh::lean_dec(v___x_2024_);
                        v___x_2032_ = leanh::lean_box(0);
                        v_isShared_2033_ = v_isSharedCheck_2045_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v_pos_2034_ = leanh::lean_ctor_get(v_inst_2020_, 0);
                leanh::lean_inc_n(v_pos_2034_, 2);
                leanh::lean_dec_ref(v_inst_2020_);
                v___x_2035_ = leanh::lean_apply_1(v_pos_2034_, v_a_2023_);
                leanh::lean_inc(v_pos_2029_);
                v___x_2036_ = leanh::lean_apply_1(v_pos_2034_, v_pos_2029_);
                v___x_2037_ = leanh::lean_apply_2(v_inst_2019_, v___x_2035_, v___x_2036_);
                v___x_2038_ = (leanh::lean_unbox(v___x_2037_) as u8);
                if v___x_2038_ == 0 {
                    leanh::lean_dec_ref(v_acc_2022_);
                    if v_isShared_2033_ == 0 {
                        v___x_2040_ = v___x_2032_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_2041_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_2041_, 0, v_pos_2029_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_2041_, 1, v_err_2030_);
                        v___x_2040_ = v_reuseFailAlloc_2041_;
                        state = 2;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v_err_2030_);
                    if v_isShared_2033_ == 0 {
                        leanh::lean_ctor_set_tag(v___x_2032_, 0);
                        leanh::lean_ctor_set(v___x_2032_, 1, v_acc_2022_);
                        v___x_2043_ = v___x_2032_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_2044_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_2044_, 0, v_pos_2029_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_2044_, 1, v_acc_2022_);
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
    mut v_00_u03b1_2046_: *mut leanh::LeanObject,
    mut v_00_u03b9_2047_: *mut leanh::LeanObject,
    mut v_elem_2048_: *mut leanh::LeanObject,
    mut v_idx_2049_: *mut leanh::LeanObject,
    mut v_inst_2050_: *mut leanh::LeanObject,
    mut v_inst_2051_: *mut leanh::LeanObject,
    mut v_inst_2052_: *mut leanh::LeanObject,
    mut v_p_2053_: *mut leanh::LeanObject,
    mut v_acc_2054_: *mut leanh::LeanObject,
    mut v_a_2055_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2056_: *mut leanh::LeanObject = core::ptr::null_mut();
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
    mut v_00_u03b1_2057_: *mut leanh::LeanObject,
    mut v_00_u03b9_2058_: *mut leanh::LeanObject,
    mut v_elem_2059_: *mut leanh::LeanObject,
    mut v_idx_2060_: *mut leanh::LeanObject,
    mut v_inst_2061_: *mut leanh::LeanObject,
    mut v_inst_2062_: *mut leanh::LeanObject,
    mut v_inst_2063_: *mut leanh::LeanObject,
    mut v_p_2064_: *mut leanh::LeanObject,
    mut v_acc_2065_: *mut leanh::LeanObject,
    mut v_a_2066_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2067_: *mut leanh::LeanObject = core::ptr::null_mut();
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
    leanh::lean_dec_ref(v_inst_2062_);
    return v_res_2067_;
}
pub unsafe fn l_Std_Internal_Parsec_many___redArg(
    mut v_inst_2070_: *mut leanh::LeanObject,
    mut v_inst_2071_: *mut leanh::LeanObject,
    mut v_p_2072_: *mut leanh::LeanObject,
    mut v_a_2073_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2074_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2075_: *mut leanh::LeanObject = core::ptr::null_mut();
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
    mut v_00_u03b1_2076_: *mut leanh::LeanObject,
    mut v_00_u03b9_2077_: *mut leanh::LeanObject,
    mut v_elem_2078_: *mut leanh::LeanObject,
    mut v_idx_2079_: *mut leanh::LeanObject,
    mut v_inst_2080_: *mut leanh::LeanObject,
    mut v_inst_2081_: *mut leanh::LeanObject,
    mut v_inst_2082_: *mut leanh::LeanObject,
    mut v_p_2083_: *mut leanh::LeanObject,
    mut v_a_2084_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2085_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2086_: *mut leanh::LeanObject = core::ptr::null_mut();
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
    mut v_00_u03b1_2087_: *mut leanh::LeanObject,
    mut v_00_u03b9_2088_: *mut leanh::LeanObject,
    mut v_elem_2089_: *mut leanh::LeanObject,
    mut v_idx_2090_: *mut leanh::LeanObject,
    mut v_inst_2091_: *mut leanh::LeanObject,
    mut v_inst_2092_: *mut leanh::LeanObject,
    mut v_inst_2093_: *mut leanh::LeanObject,
    mut v_p_2094_: *mut leanh::LeanObject,
    mut v_a_2095_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2096_: *mut leanh::LeanObject = core::ptr::null_mut();
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
    leanh::lean_dec_ref(v_inst_2092_);
    return v_res_2096_;
}
pub unsafe fn l_Std_Internal_Parsec_many1___redArg(
    mut v_inst_2097_: *mut leanh::LeanObject,
    mut v_inst_2098_: *mut leanh::LeanObject,
    mut v_p_2099_: *mut leanh::LeanObject,
    mut v_a_2100_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2101_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_pos_2102_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_res_2103_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2104_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2105_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2106_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2107_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_pos_2108_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_err_2109_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2111_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2112_: u8 = 0;
    let mut v___x_2114_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2115_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2116_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                leanh::lean_inc_ref(v_p_2099_);
                v___x_2101_ = leanh::lean_apply_1(v_p_2099_, v_a_2100_);
                if leanh::lean_obj_tag(v___x_2101_) == 0 {
                    v_pos_2102_ = leanh::lean_ctor_get(v___x_2101_, 0);
                    leanh::lean_inc(v_pos_2102_);
                    v_res_2103_ = leanh::lean_ctor_get(v___x_2101_, 1);
                    leanh::lean_inc(v_res_2103_);
                    leanh::lean_dec_ref_known(v___x_2101_, 2);
                    v___x_2104_ = leanh::lean_unsigned_to_nat(1);
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
                    leanh::lean_dec_ref(v_p_2099_);
                    leanh::lean_dec_ref(v_inst_2098_);
                    leanh::lean_dec_ref(v_inst_2097_);
                    v_pos_2108_ = leanh::lean_ctor_get(v___x_2101_, 0);
                    v_err_2109_ = leanh::lean_ctor_get(v___x_2101_, 1);
                    v_isSharedCheck_2116_ = (!leanh::lean_is_exclusive(v___x_2101_)) as u8;
                    if v_isSharedCheck_2116_ == 0 {
                        v___x_2111_ = v___x_2101_;
                        v_isShared_2112_ = v_isSharedCheck_2116_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_err_2109_);
                        leanh::lean_inc(v_pos_2108_);
                        leanh::lean_dec(v___x_2101_);
                        v___x_2111_ = leanh::lean_box(0);
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
                    v_reuseFailAlloc_2115_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2115_, 0, v_pos_2108_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2115_, 1, v_err_2109_);
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
    mut v_00_u03b1_2117_: *mut leanh::LeanObject,
    mut v_00_u03b9_2118_: *mut leanh::LeanObject,
    mut v_elem_2119_: *mut leanh::LeanObject,
    mut v_idx_2120_: *mut leanh::LeanObject,
    mut v_inst_2121_: *mut leanh::LeanObject,
    mut v_inst_2122_: *mut leanh::LeanObject,
    mut v_inst_2123_: *mut leanh::LeanObject,
    mut v_p_2124_: *mut leanh::LeanObject,
    mut v_a_2125_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2126_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_pos_2127_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_res_2128_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2129_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2130_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2131_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2132_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_pos_2133_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_err_2134_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2136_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2137_: u8 = 0;
    let mut v___x_2139_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2140_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2141_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                leanh::lean_inc_ref(v_p_2124_);
                v___x_2126_ = leanh::lean_apply_1(v_p_2124_, v_a_2125_);
                if leanh::lean_obj_tag(v___x_2126_) == 0 {
                    v_pos_2127_ = leanh::lean_ctor_get(v___x_2126_, 0);
                    leanh::lean_inc(v_pos_2127_);
                    v_res_2128_ = leanh::lean_ctor_get(v___x_2126_, 1);
                    leanh::lean_inc(v_res_2128_);
                    leanh::lean_dec_ref_known(v___x_2126_, 2);
                    v___x_2129_ = leanh::lean_unsigned_to_nat(1);
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
                    leanh::lean_dec_ref(v_p_2124_);
                    leanh::lean_dec_ref(v_inst_2123_);
                    leanh::lean_dec_ref(v_inst_2121_);
                    v_pos_2133_ = leanh::lean_ctor_get(v___x_2126_, 0);
                    v_err_2134_ = leanh::lean_ctor_get(v___x_2126_, 1);
                    v_isSharedCheck_2141_ = (!leanh::lean_is_exclusive(v___x_2126_)) as u8;
                    if v_isSharedCheck_2141_ == 0 {
                        v___x_2136_ = v___x_2126_;
                        v_isShared_2137_ = v_isSharedCheck_2141_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_err_2134_);
                        leanh::lean_inc(v_pos_2133_);
                        leanh::lean_dec(v___x_2126_);
                        v___x_2136_ = leanh::lean_box(0);
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
                    v_reuseFailAlloc_2140_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2140_, 0, v_pos_2133_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2140_, 1, v_err_2134_);
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
    mut v_00_u03b1_2142_: *mut leanh::LeanObject,
    mut v_00_u03b9_2143_: *mut leanh::LeanObject,
    mut v_elem_2144_: *mut leanh::LeanObject,
    mut v_idx_2145_: *mut leanh::LeanObject,
    mut v_inst_2146_: *mut leanh::LeanObject,
    mut v_inst_2147_: *mut leanh::LeanObject,
    mut v_inst_2148_: *mut leanh::LeanObject,
    mut v_p_2149_: *mut leanh::LeanObject,
    mut v_a_2150_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2151_: *mut leanh::LeanObject = core::ptr::null_mut();
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
    leanh::lean_dec_ref(v_inst_2147_);
    return v_res_2151_;
}
pub unsafe fn l_Std_Internal_Parsec_any___redArg(
    mut v_inst_2152_: *mut leanh::LeanObject,
    mut v_it_2153_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_hasNext_2154_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_next_x27_2155_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_curr_x27_2156_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2157_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2158_: u8 = 0;
    v_hasNext_2154_ = leanh::lean_ctor_get(v_inst_2152_, 3);
    leanh::lean_inc_ref(v_hasNext_2154_);
    v_next_x27_2155_ = leanh::lean_ctor_get(v_inst_2152_, 4);
    leanh::lean_inc(v_next_x27_2155_);
    v_curr_x27_2156_ = leanh::lean_ctor_get(v_inst_2152_, 5);
    leanh::lean_inc(v_curr_x27_2156_);
    leanh::lean_dec_ref(v_inst_2152_);
    leanh::lean_inc(v_it_2153_);
    v___x_2157_ = leanh::lean_apply_1(v_hasNext_2154_, v_it_2153_);
    v___x_2158_ = (leanh::lean_unbox(v___x_2157_) as u8);
    if v___x_2158_ == 0 {
        let mut v___x_2159_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2160_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_curr_x27_2156_);
        leanh::lean_dec(v_next_x27_2155_);
        v___x_2159_ = leanh::lean_box(0);
        v___x_2160_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
        leanh::lean_ctor_set(v___x_2160_, 0, v_it_2153_);
        leanh::lean_ctor_set(v___x_2160_, 1, v___x_2159_);
        return v___x_2160_;
    } else {
        let mut v_c_2161_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_it_x27_2162_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2163_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_inc(v_it_2153_);
        v_c_2161_ =
            leanh::lean_apply_2(v_curr_x27_2156_, v_it_2153_, leanh::lean_box(0));
        v_it_x27_2162_ =
            leanh::lean_apply_2(v_next_x27_2155_, v_it_2153_, leanh::lean_box(0));
        v___x_2163_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
        leanh::lean_ctor_set(v___x_2163_, 0, v_it_x27_2162_);
        leanh::lean_ctor_set(v___x_2163_, 1, v_c_2161_);
        return v___x_2163_;
    }
}
pub unsafe fn l_Std_Internal_Parsec_any(
    mut v_00_u03b9_2164_: *mut leanh::LeanObject,
    mut v_elem_2165_: *mut leanh::LeanObject,
    mut v_idx_2166_: *mut leanh::LeanObject,
    mut v_inst_2167_: *mut leanh::LeanObject,
    mut v_inst_2168_: *mut leanh::LeanObject,
    mut v_inst_2169_: *mut leanh::LeanObject,
    mut v_it_2170_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_hasNext_2171_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_next_x27_2172_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_curr_x27_2173_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2174_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2175_: u8 = 0;
    v_hasNext_2171_ = leanh::lean_ctor_get(v_inst_2169_, 3);
    leanh::lean_inc_ref(v_hasNext_2171_);
    v_next_x27_2172_ = leanh::lean_ctor_get(v_inst_2169_, 4);
    leanh::lean_inc(v_next_x27_2172_);
    v_curr_x27_2173_ = leanh::lean_ctor_get(v_inst_2169_, 5);
    leanh::lean_inc(v_curr_x27_2173_);
    leanh::lean_dec_ref(v_inst_2169_);
    leanh::lean_inc(v_it_2170_);
    v___x_2174_ = leanh::lean_apply_1(v_hasNext_2171_, v_it_2170_);
    v___x_2175_ = (leanh::lean_unbox(v___x_2174_) as u8);
    if v___x_2175_ == 0 {
        let mut v___x_2176_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2177_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_curr_x27_2173_);
        leanh::lean_dec(v_next_x27_2172_);
        v___x_2176_ = leanh::lean_box(0);
        v___x_2177_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
        leanh::lean_ctor_set(v___x_2177_, 0, v_it_2170_);
        leanh::lean_ctor_set(v___x_2177_, 1, v___x_2176_);
        return v___x_2177_;
    } else {
        let mut v_c_2178_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_it_x27_2179_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2180_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_inc(v_it_2170_);
        v_c_2178_ =
            leanh::lean_apply_2(v_curr_x27_2173_, v_it_2170_, leanh::lean_box(0));
        v_it_x27_2179_ =
            leanh::lean_apply_2(v_next_x27_2172_, v_it_2170_, leanh::lean_box(0));
        v___x_2180_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
        leanh::lean_ctor_set(v___x_2180_, 0, v_it_x27_2179_);
        leanh::lean_ctor_set(v___x_2180_, 1, v_c_2178_);
        return v___x_2180_;
    }
}
pub unsafe fn l_Std_Internal_Parsec_any___boxed(
    mut v_00_u03b9_2181_: *mut leanh::LeanObject,
    mut v_elem_2182_: *mut leanh::LeanObject,
    mut v_idx_2183_: *mut leanh::LeanObject,
    mut v_inst_2184_: *mut leanh::LeanObject,
    mut v_inst_2185_: *mut leanh::LeanObject,
    mut v_inst_2186_: *mut leanh::LeanObject,
    mut v_it_2187_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2188_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2188_ = l_Std_Internal_Parsec_any(
        v_00_u03b9_2181_,
        v_elem_2182_,
        v_idx_2183_,
        v_inst_2184_,
        v_inst_2185_,
        v_inst_2186_,
        v_it_2187_,
    );
    leanh::lean_dec_ref(v_inst_2185_);
    leanh::lean_dec_ref(v_inst_2184_);
    return v_res_2188_;
}
pub unsafe fn l_Std_Internal_Parsec_satisfy___redArg(
    mut v_inst_2192_: *mut leanh::LeanObject,
    mut v_p_2193_: *mut leanh::LeanObject,
    mut v_a_2194_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_hasNext_2195_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_next_x27_2196_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_curr_x27_2197_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2198_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2199_: u8 = 0;
    v_hasNext_2195_ = leanh::lean_ctor_get(v_inst_2192_, 3);
    leanh::lean_inc_ref(v_hasNext_2195_);
    v_next_x27_2196_ = leanh::lean_ctor_get(v_inst_2192_, 4);
    leanh::lean_inc(v_next_x27_2196_);
    v_curr_x27_2197_ = leanh::lean_ctor_get(v_inst_2192_, 5);
    leanh::lean_inc(v_curr_x27_2197_);
    leanh::lean_dec_ref(v_inst_2192_);
    leanh::lean_inc(v_a_2194_);
    v___x_2198_ = leanh::lean_apply_1(v_hasNext_2195_, v_a_2194_);
    v___x_2199_ = (leanh::lean_unbox(v___x_2198_) as u8);
    if v___x_2199_ == 0 {
        let mut v___x_2200_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2201_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_curr_x27_2197_);
        leanh::lean_dec(v_next_x27_2196_);
        leanh::lean_dec_ref(v_p_2193_);
        v___x_2200_ = leanh::lean_box(0);
        v___x_2201_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
        leanh::lean_ctor_set(v___x_2201_, 0, v_a_2194_);
        leanh::lean_ctor_set(v___x_2201_, 1, v___x_2200_);
        return v___x_2201_;
    } else {
        let mut v_c_2202_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_it_x27_2203_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2204_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2205_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2206_: u8 = 0;
        leanh::lean_inc_n(v_a_2194_, 2);
        v_c_2202_ =
            leanh::lean_apply_2(v_curr_x27_2197_, v_a_2194_, leanh::lean_box(0));
        v_it_x27_2203_ =
            leanh::lean_apply_2(v_next_x27_2196_, v_a_2194_, leanh::lean_box(0));
        leanh::lean_inc(v_c_2202_);
        v___x_2204_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
        leanh::lean_ctor_set(v___x_2204_, 0, v_it_x27_2203_);
        leanh::lean_ctor_set(v___x_2204_, 1, v_c_2202_);
        v___x_2205_ = leanh::lean_apply_1(v_p_2193_, v_c_2202_);
        v___x_2206_ = (leanh::lean_unbox(v___x_2205_) as u8);
        if v___x_2206_ == 0 {
            let mut v___x_2207_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_2208_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec_ref_known(v___x_2204_, 2);
            v___x_2207_ = l_Std_Internal_Parsec_satisfy___redArg___closed__1;
            v___x_2208_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
            leanh::lean_ctor_set(v___x_2208_, 0, v_a_2194_);
            leanh::lean_ctor_set(v___x_2208_, 1, v___x_2207_);
            return v___x_2208_;
        } else {
            leanh::lean_dec(v_a_2194_);
            return v___x_2204_;
        }
    }
}
pub unsafe fn l_Std_Internal_Parsec_satisfy(
    mut v_00_u03b9_2209_: *mut leanh::LeanObject,
    mut v_elem_2210_: *mut leanh::LeanObject,
    mut v_idx_2211_: *mut leanh::LeanObject,
    mut v_inst_2212_: *mut leanh::LeanObject,
    mut v_inst_2213_: *mut leanh::LeanObject,
    mut v_inst_2214_: *mut leanh::LeanObject,
    mut v_p_2215_: *mut leanh::LeanObject,
    mut v_a_2216_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_hasNext_2217_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_next_x27_2218_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_curr_x27_2219_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2220_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2221_: u8 = 0;
    v_hasNext_2217_ = leanh::lean_ctor_get(v_inst_2214_, 3);
    leanh::lean_inc_ref(v_hasNext_2217_);
    v_next_x27_2218_ = leanh::lean_ctor_get(v_inst_2214_, 4);
    leanh::lean_inc(v_next_x27_2218_);
    v_curr_x27_2219_ = leanh::lean_ctor_get(v_inst_2214_, 5);
    leanh::lean_inc(v_curr_x27_2219_);
    leanh::lean_dec_ref(v_inst_2214_);
    leanh::lean_inc(v_a_2216_);
    v___x_2220_ = leanh::lean_apply_1(v_hasNext_2217_, v_a_2216_);
    v___x_2221_ = (leanh::lean_unbox(v___x_2220_) as u8);
    if v___x_2221_ == 0 {
        let mut v___x_2222_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2223_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_curr_x27_2219_);
        leanh::lean_dec(v_next_x27_2218_);
        leanh::lean_dec_ref(v_p_2215_);
        v___x_2222_ = leanh::lean_box(0);
        v___x_2223_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
        leanh::lean_ctor_set(v___x_2223_, 0, v_a_2216_);
        leanh::lean_ctor_set(v___x_2223_, 1, v___x_2222_);
        return v___x_2223_;
    } else {
        let mut v_c_2224_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_it_x27_2225_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2226_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2227_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2228_: u8 = 0;
        leanh::lean_inc_n(v_a_2216_, 2);
        v_c_2224_ =
            leanh::lean_apply_2(v_curr_x27_2219_, v_a_2216_, leanh::lean_box(0));
        v_it_x27_2225_ =
            leanh::lean_apply_2(v_next_x27_2218_, v_a_2216_, leanh::lean_box(0));
        leanh::lean_inc(v_c_2224_);
        v___x_2226_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
        leanh::lean_ctor_set(v___x_2226_, 0, v_it_x27_2225_);
        leanh::lean_ctor_set(v___x_2226_, 1, v_c_2224_);
        v___x_2227_ = leanh::lean_apply_1(v_p_2215_, v_c_2224_);
        v___x_2228_ = (leanh::lean_unbox(v___x_2227_) as u8);
        if v___x_2228_ == 0 {
            let mut v___x_2229_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_2230_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec_ref_known(v___x_2226_, 2);
            v___x_2229_ = l_Std_Internal_Parsec_satisfy___redArg___closed__1;
            v___x_2230_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
            leanh::lean_ctor_set(v___x_2230_, 0, v_a_2216_);
            leanh::lean_ctor_set(v___x_2230_, 1, v___x_2229_);
            return v___x_2230_;
        } else {
            leanh::lean_dec(v_a_2216_);
            return v___x_2226_;
        }
    }
}
pub unsafe fn l_Std_Internal_Parsec_satisfy___boxed(
    mut v_00_u03b9_2231_: *mut leanh::LeanObject,
    mut v_elem_2232_: *mut leanh::LeanObject,
    mut v_idx_2233_: *mut leanh::LeanObject,
    mut v_inst_2234_: *mut leanh::LeanObject,
    mut v_inst_2235_: *mut leanh::LeanObject,
    mut v_inst_2236_: *mut leanh::LeanObject,
    mut v_p_2237_: *mut leanh::LeanObject,
    mut v_a_2238_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2239_: *mut leanh::LeanObject = core::ptr::null_mut();
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
    leanh::lean_dec_ref(v_inst_2235_);
    leanh::lean_dec_ref(v_inst_2234_);
    return v_res_2239_;
}
pub unsafe fn l_Std_Internal_Parsec_notFollowedBy___redArg(
    mut v_p_2240_: *mut leanh::LeanObject,
    mut v_it_2241_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2242_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2244_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2245_: u8 = 0;
    let mut v___x_2246_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2248_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2249_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2250_: u8 = 0;
    let mut v_unused_2251_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2252_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2254_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2255_: u8 = 0;
    let mut v___x_2256_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2258_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2259_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2260_: u8 = 0;
    let mut v_unused_2261_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2262_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                leanh::lean_inc(v_it_2241_);
                v___x_2242_ = leanh::lean_apply_1(v_p_2240_, v_it_2241_);
                if leanh::lean_obj_tag(v___x_2242_) == 0 {
                    v_isSharedCheck_2250_ = (!leanh::lean_is_exclusive(v___x_2242_)) as u8;
                    if v_isSharedCheck_2250_ == 0 {
                        v_unused_2251_ = leanh::lean_ctor_get(v___x_2242_, 1);
                        leanh::lean_dec(v_unused_2251_);
                        v_unused_2252_ = leanh::lean_ctor_get(v___x_2242_, 0);
                        leanh::lean_dec(v_unused_2252_);
                        v___x_2244_ = v___x_2242_;
                        v_isShared_2245_ = v_isSharedCheck_2250_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_dec(v___x_2242_);
                        v___x_2244_ = leanh::lean_box(0);
                        v_isShared_2245_ = v_isSharedCheck_2250_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_isSharedCheck_2260_ = (!leanh::lean_is_exclusive(v___x_2242_)) as u8;
                    if v_isSharedCheck_2260_ == 0 {
                        v_unused_2261_ = leanh::lean_ctor_get(v___x_2242_, 1);
                        leanh::lean_dec(v_unused_2261_);
                        v_unused_2262_ = leanh::lean_ctor_get(v___x_2242_, 0);
                        leanh::lean_dec(v_unused_2262_);
                        v___x_2254_ = v___x_2242_;
                        v_isShared_2255_ = v_isSharedCheck_2260_;
                        state = 3;
                        continue;
                    } else {
                        leanh::lean_dec(v___x_2242_);
                        v___x_2254_ = leanh::lean_box(0);
                        v_isShared_2255_ = v_isSharedCheck_2260_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v___x_2246_ = l_Std_Internal_Parsec_instInhabited___lam__0___closed__1;
                if v_isShared_2245_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_2244_, 1);
                    leanh::lean_ctor_set(v___x_2244_, 1, v___x_2246_);
                    leanh::lean_ctor_set(v___x_2244_, 0, v_it_2241_);
                    v___x_2248_ = v___x_2244_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2249_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2249_, 0, v_it_2241_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2249_, 1, v___x_2246_);
                    v___x_2248_ = v_reuseFailAlloc_2249_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_2248_;
            }
            3 => {
                v___x_2256_ = leanh::lean_box(0);
                if v_isShared_2255_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_2254_, 0);
                    leanh::lean_ctor_set(v___x_2254_, 1, v___x_2256_);
                    leanh::lean_ctor_set(v___x_2254_, 0, v_it_2241_);
                    v___x_2258_ = v___x_2254_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2259_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2259_, 0, v_it_2241_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2259_, 1, v___x_2256_);
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
    mut v_00_u03b1_2263_: *mut leanh::LeanObject,
    mut v_00_u03b9_2264_: *mut leanh::LeanObject,
    mut v_p_2265_: *mut leanh::LeanObject,
    mut v_it_2266_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2267_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2269_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2270_: u8 = 0;
    let mut v___x_2271_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2273_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2274_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2275_: u8 = 0;
    let mut v_unused_2276_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2277_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2279_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2280_: u8 = 0;
    let mut v___x_2281_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2283_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2284_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2285_: u8 = 0;
    let mut v_unused_2286_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2287_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                leanh::lean_inc(v_it_2266_);
                v___x_2267_ = leanh::lean_apply_1(v_p_2265_, v_it_2266_);
                if leanh::lean_obj_tag(v___x_2267_) == 0 {
                    v_isSharedCheck_2275_ = (!leanh::lean_is_exclusive(v___x_2267_)) as u8;
                    if v_isSharedCheck_2275_ == 0 {
                        v_unused_2276_ = leanh::lean_ctor_get(v___x_2267_, 1);
                        leanh::lean_dec(v_unused_2276_);
                        v_unused_2277_ = leanh::lean_ctor_get(v___x_2267_, 0);
                        leanh::lean_dec(v_unused_2277_);
                        v___x_2269_ = v___x_2267_;
                        v_isShared_2270_ = v_isSharedCheck_2275_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_dec(v___x_2267_);
                        v___x_2269_ = leanh::lean_box(0);
                        v_isShared_2270_ = v_isSharedCheck_2275_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_isSharedCheck_2285_ = (!leanh::lean_is_exclusive(v___x_2267_)) as u8;
                    if v_isSharedCheck_2285_ == 0 {
                        v_unused_2286_ = leanh::lean_ctor_get(v___x_2267_, 1);
                        leanh::lean_dec(v_unused_2286_);
                        v_unused_2287_ = leanh::lean_ctor_get(v___x_2267_, 0);
                        leanh::lean_dec(v_unused_2287_);
                        v___x_2279_ = v___x_2267_;
                        v_isShared_2280_ = v_isSharedCheck_2285_;
                        state = 3;
                        continue;
                    } else {
                        leanh::lean_dec(v___x_2267_);
                        v___x_2279_ = leanh::lean_box(0);
                        v_isShared_2280_ = v_isSharedCheck_2285_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v___x_2271_ = l_Std_Internal_Parsec_instInhabited___lam__0___closed__1;
                if v_isShared_2270_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_2269_, 1);
                    leanh::lean_ctor_set(v___x_2269_, 1, v___x_2271_);
                    leanh::lean_ctor_set(v___x_2269_, 0, v_it_2266_);
                    v___x_2273_ = v___x_2269_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2274_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2274_, 0, v_it_2266_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2274_, 1, v___x_2271_);
                    v___x_2273_ = v_reuseFailAlloc_2274_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_2273_;
            }
            3 => {
                v___x_2281_ = leanh::lean_box(0);
                if v_isShared_2280_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_2279_, 0);
                    leanh::lean_ctor_set(v___x_2279_, 1, v___x_2281_);
                    leanh::lean_ctor_set(v___x_2279_, 0, v_it_2266_);
                    v___x_2283_ = v___x_2279_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2284_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2284_, 0, v_it_2266_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2284_, 1, v___x_2281_);
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
    mut v_inst_2288_: *mut leanh::LeanObject,
    mut v_it_2289_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_hasNext_2290_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_curr_x27_2291_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2292_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2293_: u8 = 0;
    v_hasNext_2290_ = leanh::lean_ctor_get(v_inst_2288_, 3);
    leanh::lean_inc_ref(v_hasNext_2290_);
    v_curr_x27_2291_ = leanh::lean_ctor_get(v_inst_2288_, 5);
    leanh::lean_inc(v_curr_x27_2291_);
    leanh::lean_dec_ref(v_inst_2288_);
    leanh::lean_inc(v_it_2289_);
    v___x_2292_ = leanh::lean_apply_1(v_hasNext_2290_, v_it_2289_);
    v___x_2293_ = (leanh::lean_unbox(v___x_2292_) as u8);
    if v___x_2293_ == 0 {
        let mut v___x_2294_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2295_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_curr_x27_2291_);
        v___x_2294_ = leanh::lean_box(0);
        v___x_2295_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
        leanh::lean_ctor_set(v___x_2295_, 0, v_it_2289_);
        leanh::lean_ctor_set(v___x_2295_, 1, v___x_2294_);
        return v___x_2295_;
    } else {
        let mut v___x_2296_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2297_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2298_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_inc(v_it_2289_);
        v___x_2296_ =
            leanh::lean_apply_2(v_curr_x27_2291_, v_it_2289_, leanh::lean_box(0));
        v___x_2297_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
        leanh::lean_ctor_set(v___x_2297_, 0, v___x_2296_);
        v___x_2298_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
        leanh::lean_ctor_set(v___x_2298_, 0, v_it_2289_);
        leanh::lean_ctor_set(v___x_2298_, 1, v___x_2297_);
        return v___x_2298_;
    }
}
pub unsafe fn l_Std_Internal_Parsec_peek_x3f(
    mut v_00_u03b9_2299_: *mut leanh::LeanObject,
    mut v_elem_2300_: *mut leanh::LeanObject,
    mut v_idx_2301_: *mut leanh::LeanObject,
    mut v_inst_2302_: *mut leanh::LeanObject,
    mut v_inst_2303_: *mut leanh::LeanObject,
    mut v_inst_2304_: *mut leanh::LeanObject,
    mut v_it_2305_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_hasNext_2306_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_curr_x27_2307_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2308_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2309_: u8 = 0;
    v_hasNext_2306_ = leanh::lean_ctor_get(v_inst_2304_, 3);
    leanh::lean_inc_ref(v_hasNext_2306_);
    v_curr_x27_2307_ = leanh::lean_ctor_get(v_inst_2304_, 5);
    leanh::lean_inc(v_curr_x27_2307_);
    leanh::lean_dec_ref(v_inst_2304_);
    leanh::lean_inc(v_it_2305_);
    v___x_2308_ = leanh::lean_apply_1(v_hasNext_2306_, v_it_2305_);
    v___x_2309_ = (leanh::lean_unbox(v___x_2308_) as u8);
    if v___x_2309_ == 0 {
        let mut v___x_2310_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2311_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_curr_x27_2307_);
        v___x_2310_ = leanh::lean_box(0);
        v___x_2311_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
        leanh::lean_ctor_set(v___x_2311_, 0, v_it_2305_);
        leanh::lean_ctor_set(v___x_2311_, 1, v___x_2310_);
        return v___x_2311_;
    } else {
        let mut v___x_2312_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2313_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2314_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_inc(v_it_2305_);
        v___x_2312_ =
            leanh::lean_apply_2(v_curr_x27_2307_, v_it_2305_, leanh::lean_box(0));
        v___x_2313_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
        leanh::lean_ctor_set(v___x_2313_, 0, v___x_2312_);
        v___x_2314_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
        leanh::lean_ctor_set(v___x_2314_, 0, v_it_2305_);
        leanh::lean_ctor_set(v___x_2314_, 1, v___x_2313_);
        return v___x_2314_;
    }
}
pub unsafe fn l_Std_Internal_Parsec_peek_x3f___boxed(
    mut v_00_u03b9_2315_: *mut leanh::LeanObject,
    mut v_elem_2316_: *mut leanh::LeanObject,
    mut v_idx_2317_: *mut leanh::LeanObject,
    mut v_inst_2318_: *mut leanh::LeanObject,
    mut v_inst_2319_: *mut leanh::LeanObject,
    mut v_inst_2320_: *mut leanh::LeanObject,
    mut v_it_2321_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2322_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2322_ = l_Std_Internal_Parsec_peek_x3f(
        v_00_u03b9_2315_,
        v_elem_2316_,
        v_idx_2317_,
        v_inst_2318_,
        v_inst_2319_,
        v_inst_2320_,
        v_it_2321_,
    );
    leanh::lean_dec_ref(v_inst_2319_);
    leanh::lean_dec_ref(v_inst_2318_);
    return v_res_2322_;
}
pub unsafe fn l_Std_Internal_Parsec_peekWhen_x3f___redArg(
    mut v_inst_2323_: *mut leanh::LeanObject,
    mut v_p_2324_: *mut leanh::LeanObject,
    mut v_a_2325_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_hasNext_2326_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_curr_x27_2327_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2328_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2329_: u8 = 0;
    v_hasNext_2326_ = leanh::lean_ctor_get(v_inst_2323_, 3);
    leanh::lean_inc_ref(v_hasNext_2326_);
    v_curr_x27_2327_ = leanh::lean_ctor_get(v_inst_2323_, 5);
    leanh::lean_inc(v_curr_x27_2327_);
    leanh::lean_dec_ref(v_inst_2323_);
    leanh::lean_inc(v_a_2325_);
    v___x_2328_ = leanh::lean_apply_1(v_hasNext_2326_, v_a_2325_);
    v___x_2329_ = (leanh::lean_unbox(v___x_2328_) as u8);
    if v___x_2329_ == 0 {
        let mut v___x_2330_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2331_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_curr_x27_2327_);
        leanh::lean_dec_ref(v_p_2324_);
        v___x_2330_ = leanh::lean_box(0);
        v___x_2331_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
        leanh::lean_ctor_set(v___x_2331_, 0, v_a_2325_);
        leanh::lean_ctor_set(v___x_2331_, 1, v___x_2330_);
        return v___x_2331_;
    } else {
        let mut v___x_2332_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2333_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2334_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2335_: u8 = 0;
        leanh::lean_inc(v_a_2325_);
        v___x_2332_ =
            leanh::lean_apply_2(v_curr_x27_2327_, v_a_2325_, leanh::lean_box(0));
        leanh::lean_inc(v___x_2332_);
        v___x_2333_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
        leanh::lean_ctor_set(v___x_2333_, 0, v___x_2332_);
        v___x_2334_ = leanh::lean_apply_1(v_p_2324_, v___x_2332_);
        v___x_2335_ = (leanh::lean_unbox(v___x_2334_) as u8);
        if v___x_2335_ == 0 {
            let mut v___x_2336_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_2337_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec_ref_known(v___x_2333_, 1);
            v___x_2336_ = leanh::lean_box(0);
            v___x_2337_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
            leanh::lean_ctor_set(v___x_2337_, 0, v_a_2325_);
            leanh::lean_ctor_set(v___x_2337_, 1, v___x_2336_);
            return v___x_2337_;
        } else {
            let mut v___x_2338_: *mut leanh::LeanObject = core::ptr::null_mut();
            v___x_2338_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
            leanh::lean_ctor_set(v___x_2338_, 0, v_a_2325_);
            leanh::lean_ctor_set(v___x_2338_, 1, v___x_2333_);
            return v___x_2338_;
        }
    }
}
pub unsafe fn l_Std_Internal_Parsec_peekWhen_x3f(
    mut v_00_u03b9_2339_: *mut leanh::LeanObject,
    mut v_elem_2340_: *mut leanh::LeanObject,
    mut v_idx_2341_: *mut leanh::LeanObject,
    mut v_inst_2342_: *mut leanh::LeanObject,
    mut v_inst_2343_: *mut leanh::LeanObject,
    mut v_inst_2344_: *mut leanh::LeanObject,
    mut v_p_2345_: *mut leanh::LeanObject,
    mut v_a_2346_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_hasNext_2347_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_curr_x27_2348_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2349_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2350_: u8 = 0;
    v_hasNext_2347_ = leanh::lean_ctor_get(v_inst_2344_, 3);
    leanh::lean_inc_ref(v_hasNext_2347_);
    v_curr_x27_2348_ = leanh::lean_ctor_get(v_inst_2344_, 5);
    leanh::lean_inc(v_curr_x27_2348_);
    leanh::lean_dec_ref(v_inst_2344_);
    leanh::lean_inc(v_a_2346_);
    v___x_2349_ = leanh::lean_apply_1(v_hasNext_2347_, v_a_2346_);
    v___x_2350_ = (leanh::lean_unbox(v___x_2349_) as u8);
    if v___x_2350_ == 0 {
        let mut v___x_2351_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2352_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_curr_x27_2348_);
        leanh::lean_dec_ref(v_p_2345_);
        v___x_2351_ = leanh::lean_box(0);
        v___x_2352_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
        leanh::lean_ctor_set(v___x_2352_, 0, v_a_2346_);
        leanh::lean_ctor_set(v___x_2352_, 1, v___x_2351_);
        return v___x_2352_;
    } else {
        let mut v___x_2353_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2354_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2355_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2356_: u8 = 0;
        leanh::lean_inc(v_a_2346_);
        v___x_2353_ =
            leanh::lean_apply_2(v_curr_x27_2348_, v_a_2346_, leanh::lean_box(0));
        leanh::lean_inc(v___x_2353_);
        v___x_2354_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
        leanh::lean_ctor_set(v___x_2354_, 0, v___x_2353_);
        v___x_2355_ = leanh::lean_apply_1(v_p_2345_, v___x_2353_);
        v___x_2356_ = (leanh::lean_unbox(v___x_2355_) as u8);
        if v___x_2356_ == 0 {
            let mut v___x_2357_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_2358_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec_ref_known(v___x_2354_, 1);
            v___x_2357_ = leanh::lean_box(0);
            v___x_2358_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
            leanh::lean_ctor_set(v___x_2358_, 0, v_a_2346_);
            leanh::lean_ctor_set(v___x_2358_, 1, v___x_2357_);
            return v___x_2358_;
        } else {
            let mut v___x_2359_: *mut leanh::LeanObject = core::ptr::null_mut();
            v___x_2359_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
            leanh::lean_ctor_set(v___x_2359_, 0, v_a_2346_);
            leanh::lean_ctor_set(v___x_2359_, 1, v___x_2354_);
            return v___x_2359_;
        }
    }
}
pub unsafe fn l_Std_Internal_Parsec_peekWhen_x3f___boxed(
    mut v_00_u03b9_2360_: *mut leanh::LeanObject,
    mut v_elem_2361_: *mut leanh::LeanObject,
    mut v_idx_2362_: *mut leanh::LeanObject,
    mut v_inst_2363_: *mut leanh::LeanObject,
    mut v_inst_2364_: *mut leanh::LeanObject,
    mut v_inst_2365_: *mut leanh::LeanObject,
    mut v_p_2366_: *mut leanh::LeanObject,
    mut v_a_2367_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2368_: *mut leanh::LeanObject = core::ptr::null_mut();
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
    leanh::lean_dec_ref(v_inst_2364_);
    leanh::lean_dec_ref(v_inst_2363_);
    return v_res_2368_;
}
pub unsafe fn l_Std_Internal_Parsec_peek_x21___redArg(
    mut v_inst_2369_: *mut leanh::LeanObject,
    mut v_it_2370_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_hasNext_2371_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_curr_x27_2372_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2373_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2374_: u8 = 0;
    v_hasNext_2371_ = leanh::lean_ctor_get(v_inst_2369_, 3);
    leanh::lean_inc_ref(v_hasNext_2371_);
    v_curr_x27_2372_ = leanh::lean_ctor_get(v_inst_2369_, 5);
    leanh::lean_inc(v_curr_x27_2372_);
    leanh::lean_dec_ref(v_inst_2369_);
    leanh::lean_inc(v_it_2370_);
    v___x_2373_ = leanh::lean_apply_1(v_hasNext_2371_, v_it_2370_);
    v___x_2374_ = (leanh::lean_unbox(v___x_2373_) as u8);
    if v___x_2374_ == 0 {
        let mut v___x_2375_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2376_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_curr_x27_2372_);
        v___x_2375_ = leanh::lean_box(0);
        v___x_2376_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
        leanh::lean_ctor_set(v___x_2376_, 0, v_it_2370_);
        leanh::lean_ctor_set(v___x_2376_, 1, v___x_2375_);
        return v___x_2376_;
    } else {
        let mut v___x_2377_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2378_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_inc(v_it_2370_);
        v___x_2377_ =
            leanh::lean_apply_2(v_curr_x27_2372_, v_it_2370_, leanh::lean_box(0));
        v___x_2378_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
        leanh::lean_ctor_set(v___x_2378_, 0, v_it_2370_);
        leanh::lean_ctor_set(v___x_2378_, 1, v___x_2377_);
        return v___x_2378_;
    }
}
pub unsafe fn l_Std_Internal_Parsec_peek_x21(
    mut v_00_u03b9_2379_: *mut leanh::LeanObject,
    mut v_elem_2380_: *mut leanh::LeanObject,
    mut v_idx_2381_: *mut leanh::LeanObject,
    mut v_inst_2382_: *mut leanh::LeanObject,
    mut v_inst_2383_: *mut leanh::LeanObject,
    mut v_inst_2384_: *mut leanh::LeanObject,
    mut v_it_2385_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_hasNext_2386_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_curr_x27_2387_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2388_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2389_: u8 = 0;
    v_hasNext_2386_ = leanh::lean_ctor_get(v_inst_2384_, 3);
    leanh::lean_inc_ref(v_hasNext_2386_);
    v_curr_x27_2387_ = leanh::lean_ctor_get(v_inst_2384_, 5);
    leanh::lean_inc(v_curr_x27_2387_);
    leanh::lean_dec_ref(v_inst_2384_);
    leanh::lean_inc(v_it_2385_);
    v___x_2388_ = leanh::lean_apply_1(v_hasNext_2386_, v_it_2385_);
    v___x_2389_ = (leanh::lean_unbox(v___x_2388_) as u8);
    if v___x_2389_ == 0 {
        let mut v___x_2390_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2391_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_curr_x27_2387_);
        v___x_2390_ = leanh::lean_box(0);
        v___x_2391_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
        leanh::lean_ctor_set(v___x_2391_, 0, v_it_2385_);
        leanh::lean_ctor_set(v___x_2391_, 1, v___x_2390_);
        return v___x_2391_;
    } else {
        let mut v___x_2392_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2393_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_inc(v_it_2385_);
        v___x_2392_ =
            leanh::lean_apply_2(v_curr_x27_2387_, v_it_2385_, leanh::lean_box(0));
        v___x_2393_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
        leanh::lean_ctor_set(v___x_2393_, 0, v_it_2385_);
        leanh::lean_ctor_set(v___x_2393_, 1, v___x_2392_);
        return v___x_2393_;
    }
}
pub unsafe fn l_Std_Internal_Parsec_peek_x21___boxed(
    mut v_00_u03b9_2394_: *mut leanh::LeanObject,
    mut v_elem_2395_: *mut leanh::LeanObject,
    mut v_idx_2396_: *mut leanh::LeanObject,
    mut v_inst_2397_: *mut leanh::LeanObject,
    mut v_inst_2398_: *mut leanh::LeanObject,
    mut v_inst_2399_: *mut leanh::LeanObject,
    mut v_it_2400_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2401_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2401_ = l_Std_Internal_Parsec_peek_x21(
        v_00_u03b9_2394_,
        v_elem_2395_,
        v_idx_2396_,
        v_inst_2397_,
        v_inst_2398_,
        v_inst_2399_,
        v_it_2400_,
    );
    leanh::lean_dec_ref(v_inst_2398_);
    leanh::lean_dec_ref(v_inst_2397_);
    return v_res_2401_;
}
pub unsafe fn l_Std_Internal_Parsec_peekD___redArg(
    mut v_inst_2402_: *mut leanh::LeanObject,
    mut v_default_2403_: *mut leanh::LeanObject,
    mut v_it_2404_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_hasNext_2405_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_curr_x27_2406_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2407_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2408_: u8 = 0;
    v_hasNext_2405_ = leanh::lean_ctor_get(v_inst_2402_, 3);
    leanh::lean_inc_ref(v_hasNext_2405_);
    v_curr_x27_2406_ = leanh::lean_ctor_get(v_inst_2402_, 5);
    leanh::lean_inc(v_curr_x27_2406_);
    leanh::lean_dec_ref(v_inst_2402_);
    leanh::lean_inc(v_it_2404_);
    v___x_2407_ = leanh::lean_apply_1(v_hasNext_2405_, v_it_2404_);
    v___x_2408_ = (leanh::lean_unbox(v___x_2407_) as u8);
    if v___x_2408_ == 0 {
        let mut v___x_2409_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_curr_x27_2406_);
        v___x_2409_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
        leanh::lean_ctor_set(v___x_2409_, 0, v_it_2404_);
        leanh::lean_ctor_set(v___x_2409_, 1, v_default_2403_);
        return v___x_2409_;
    } else {
        let mut v___x_2410_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2411_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_default_2403_);
        leanh::lean_inc(v_it_2404_);
        v___x_2410_ =
            leanh::lean_apply_2(v_curr_x27_2406_, v_it_2404_, leanh::lean_box(0));
        v___x_2411_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
        leanh::lean_ctor_set(v___x_2411_, 0, v_it_2404_);
        leanh::lean_ctor_set(v___x_2411_, 1, v___x_2410_);
        return v___x_2411_;
    }
}
pub unsafe fn l_Std_Internal_Parsec_peekD(
    mut v_00_u03b9_2412_: *mut leanh::LeanObject,
    mut v_elem_2413_: *mut leanh::LeanObject,
    mut v_idx_2414_: *mut leanh::LeanObject,
    mut v_inst_2415_: *mut leanh::LeanObject,
    mut v_inst_2416_: *mut leanh::LeanObject,
    mut v_inst_2417_: *mut leanh::LeanObject,
    mut v_default_2418_: *mut leanh::LeanObject,
    mut v_it_2419_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_hasNext_2420_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_curr_x27_2421_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2422_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2423_: u8 = 0;
    v_hasNext_2420_ = leanh::lean_ctor_get(v_inst_2417_, 3);
    leanh::lean_inc_ref(v_hasNext_2420_);
    v_curr_x27_2421_ = leanh::lean_ctor_get(v_inst_2417_, 5);
    leanh::lean_inc(v_curr_x27_2421_);
    leanh::lean_dec_ref(v_inst_2417_);
    leanh::lean_inc(v_it_2419_);
    v___x_2422_ = leanh::lean_apply_1(v_hasNext_2420_, v_it_2419_);
    v___x_2423_ = (leanh::lean_unbox(v___x_2422_) as u8);
    if v___x_2423_ == 0 {
        let mut v___x_2424_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_curr_x27_2421_);
        v___x_2424_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
        leanh::lean_ctor_set(v___x_2424_, 0, v_it_2419_);
        leanh::lean_ctor_set(v___x_2424_, 1, v_default_2418_);
        return v___x_2424_;
    } else {
        let mut v___x_2425_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2426_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_default_2418_);
        leanh::lean_inc(v_it_2419_);
        v___x_2425_ =
            leanh::lean_apply_2(v_curr_x27_2421_, v_it_2419_, leanh::lean_box(0));
        v___x_2426_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
        leanh::lean_ctor_set(v___x_2426_, 0, v_it_2419_);
        leanh::lean_ctor_set(v___x_2426_, 1, v___x_2425_);
        return v___x_2426_;
    }
}
pub unsafe fn l_Std_Internal_Parsec_peekD___boxed(
    mut v_00_u03b9_2427_: *mut leanh::LeanObject,
    mut v_elem_2428_: *mut leanh::LeanObject,
    mut v_idx_2429_: *mut leanh::LeanObject,
    mut v_inst_2430_: *mut leanh::LeanObject,
    mut v_inst_2431_: *mut leanh::LeanObject,
    mut v_inst_2432_: *mut leanh::LeanObject,
    mut v_default_2433_: *mut leanh::LeanObject,
    mut v_it_2434_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2435_: *mut leanh::LeanObject = core::ptr::null_mut();
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
    leanh::lean_dec_ref(v_inst_2431_);
    leanh::lean_dec_ref(v_inst_2430_);
    return v_res_2435_;
}
pub unsafe fn l_Std_Internal_Parsec_skip___redArg(
    mut v_inst_2436_: *mut leanh::LeanObject,
    mut v_it_2437_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_hasNext_2438_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_next_x27_2439_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2440_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2441_: u8 = 0;
    v_hasNext_2438_ = leanh::lean_ctor_get(v_inst_2436_, 3);
    leanh::lean_inc_ref(v_hasNext_2438_);
    v_next_x27_2439_ = leanh::lean_ctor_get(v_inst_2436_, 4);
    leanh::lean_inc(v_next_x27_2439_);
    leanh::lean_dec_ref(v_inst_2436_);
    leanh::lean_inc(v_it_2437_);
    v___x_2440_ = leanh::lean_apply_1(v_hasNext_2438_, v_it_2437_);
    v___x_2441_ = (leanh::lean_unbox(v___x_2440_) as u8);
    if v___x_2441_ == 0 {
        let mut v___x_2442_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2443_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_next_x27_2439_);
        v___x_2442_ = leanh::lean_box(0);
        v___x_2443_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
        leanh::lean_ctor_set(v___x_2443_, 0, v_it_2437_);
        leanh::lean_ctor_set(v___x_2443_, 1, v___x_2442_);
        return v___x_2443_;
    } else {
        let mut v___x_2444_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2445_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2446_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_2444_ =
            leanh::lean_apply_2(v_next_x27_2439_, v_it_2437_, leanh::lean_box(0));
        v___x_2445_ = leanh::lean_box(0);
        v___x_2446_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
        leanh::lean_ctor_set(v___x_2446_, 0, v___x_2444_);
        leanh::lean_ctor_set(v___x_2446_, 1, v___x_2445_);
        return v___x_2446_;
    }
}
pub unsafe fn l_Std_Internal_Parsec_skip(
    mut v_00_u03b9_2447_: *mut leanh::LeanObject,
    mut v_elem_2448_: *mut leanh::LeanObject,
    mut v_idx_2449_: *mut leanh::LeanObject,
    mut v_inst_2450_: *mut leanh::LeanObject,
    mut v_inst_2451_: *mut leanh::LeanObject,
    mut v_inst_2452_: *mut leanh::LeanObject,
    mut v_it_2453_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_hasNext_2454_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_next_x27_2455_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2456_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2457_: u8 = 0;
    v_hasNext_2454_ = leanh::lean_ctor_get(v_inst_2452_, 3);
    leanh::lean_inc_ref(v_hasNext_2454_);
    v_next_x27_2455_ = leanh::lean_ctor_get(v_inst_2452_, 4);
    leanh::lean_inc(v_next_x27_2455_);
    leanh::lean_dec_ref(v_inst_2452_);
    leanh::lean_inc(v_it_2453_);
    v___x_2456_ = leanh::lean_apply_1(v_hasNext_2454_, v_it_2453_);
    v___x_2457_ = (leanh::lean_unbox(v___x_2456_) as u8);
    if v___x_2457_ == 0 {
        let mut v___x_2458_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2459_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_next_x27_2455_);
        v___x_2458_ = leanh::lean_box(0);
        v___x_2459_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
        leanh::lean_ctor_set(v___x_2459_, 0, v_it_2453_);
        leanh::lean_ctor_set(v___x_2459_, 1, v___x_2458_);
        return v___x_2459_;
    } else {
        let mut v___x_2460_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2461_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2462_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_2460_ =
            leanh::lean_apply_2(v_next_x27_2455_, v_it_2453_, leanh::lean_box(0));
        v___x_2461_ = leanh::lean_box(0);
        v___x_2462_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
        leanh::lean_ctor_set(v___x_2462_, 0, v___x_2460_);
        leanh::lean_ctor_set(v___x_2462_, 1, v___x_2461_);
        return v___x_2462_;
    }
}
pub unsafe fn l_Std_Internal_Parsec_skip___boxed(
    mut v_00_u03b9_2463_: *mut leanh::LeanObject,
    mut v_elem_2464_: *mut leanh::LeanObject,
    mut v_idx_2465_: *mut leanh::LeanObject,
    mut v_inst_2466_: *mut leanh::LeanObject,
    mut v_inst_2467_: *mut leanh::LeanObject,
    mut v_inst_2468_: *mut leanh::LeanObject,
    mut v_it_2469_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2470_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2470_ = l_Std_Internal_Parsec_skip(
        v_00_u03b9_2463_,
        v_elem_2464_,
        v_idx_2465_,
        v_inst_2466_,
        v_inst_2467_,
        v_inst_2468_,
        v_it_2469_,
    );
    leanh::lean_dec_ref(v_inst_2467_);
    leanh::lean_dec_ref(v_inst_2466_);
    return v_res_2470_;
}
pub unsafe fn l_Std_Internal_Parsec_manyCharsCore___redArg(
    mut v_inst_2471_: *mut leanh::LeanObject,
    mut v_inst_2472_: *mut leanh::LeanObject,
    mut v_p_2473_: *mut leanh::LeanObject,
    mut v_acc_2474_: *mut leanh::LeanObject,
    mut v_a_2475_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2476_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_pos_2477_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_res_2478_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2479_: u32 = 0;
    let mut v___x_2480_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_pos_2482_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_err_2483_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2485_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2486_: u8 = 0;
    let mut v_pos_2487_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2488_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2489_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2490_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2491_: u8 = 0;
    let mut v___x_2493_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2494_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2496_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2497_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2498_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                leanh::lean_inc_ref(v_p_2473_);
                leanh::lean_inc(v_a_2475_);
                v___x_2476_ = leanh::lean_apply_1(v_p_2473_, v_a_2475_);
                if leanh::lean_obj_tag(v___x_2476_) == 0 {
                    leanh::lean_dec(v_a_2475_);
                    v_pos_2477_ = leanh::lean_ctor_get(v___x_2476_, 0);
                    leanh::lean_inc(v_pos_2477_);
                    v_res_2478_ = leanh::lean_ctor_get(v___x_2476_, 1);
                    leanh::lean_inc(v_res_2478_);
                    leanh::lean_dec_ref_known(v___x_2476_, 2);
                    v___x_2479_ = leanh::lean_unbox_uint32(v_res_2478_);
                    leanh::lean_dec(v_res_2478_);
                    v___x_2480_ = lean_string_push(v_acc_2474_, v___x_2479_);
                    v_acc_2474_ = v___x_2480_;
                    v_a_2475_ = v_pos_2477_;
                    state = 0;
                    continue;
                } else {
                    leanh::lean_dec_ref(v_p_2473_);
                    v_pos_2482_ = leanh::lean_ctor_get(v___x_2476_, 0);
                    v_err_2483_ = leanh::lean_ctor_get(v___x_2476_, 1);
                    v_isSharedCheck_2498_ = (!leanh::lean_is_exclusive(v___x_2476_)) as u8;
                    if v_isSharedCheck_2498_ == 0 {
                        v___x_2485_ = v___x_2476_;
                        v_isShared_2486_ = v_isSharedCheck_2498_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_err_2483_);
                        leanh::lean_inc(v_pos_2482_);
                        leanh::lean_dec(v___x_2476_);
                        v___x_2485_ = leanh::lean_box(0);
                        v_isShared_2486_ = v_isSharedCheck_2498_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v_pos_2487_ = leanh::lean_ctor_get(v_inst_2472_, 0);
                leanh::lean_inc_n(v_pos_2487_, 2);
                leanh::lean_dec_ref(v_inst_2472_);
                v___x_2488_ = leanh::lean_apply_1(v_pos_2487_, v_a_2475_);
                leanh::lean_inc(v_pos_2482_);
                v___x_2489_ = leanh::lean_apply_1(v_pos_2487_, v_pos_2482_);
                v___x_2490_ = leanh::lean_apply_2(v_inst_2471_, v___x_2488_, v___x_2489_);
                v___x_2491_ = (leanh::lean_unbox(v___x_2490_) as u8);
                if v___x_2491_ == 0 {
                    leanh::lean_dec_ref(v_acc_2474_);
                    if v_isShared_2486_ == 0 {
                        v___x_2493_ = v___x_2485_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_2494_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_2494_, 0, v_pos_2482_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_2494_, 1, v_err_2483_);
                        v___x_2493_ = v_reuseFailAlloc_2494_;
                        state = 2;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v_err_2483_);
                    if v_isShared_2486_ == 0 {
                        leanh::lean_ctor_set_tag(v___x_2485_, 0);
                        leanh::lean_ctor_set(v___x_2485_, 1, v_acc_2474_);
                        v___x_2496_ = v___x_2485_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_2497_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_2497_, 0, v_pos_2482_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_2497_, 1, v_acc_2474_);
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
    mut v_00_u03b9_2499_: *mut leanh::LeanObject,
    mut v_elem_2500_: *mut leanh::LeanObject,
    mut v_idx_2501_: *mut leanh::LeanObject,
    mut v_inst_2502_: *mut leanh::LeanObject,
    mut v_inst_2503_: *mut leanh::LeanObject,
    mut v_inst_2504_: *mut leanh::LeanObject,
    mut v_p_2505_: *mut leanh::LeanObject,
    mut v_acc_2506_: *mut leanh::LeanObject,
    mut v_a_2507_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2508_: *mut leanh::LeanObject = core::ptr::null_mut();
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
    mut v_00_u03b9_2509_: *mut leanh::LeanObject,
    mut v_elem_2510_: *mut leanh::LeanObject,
    mut v_idx_2511_: *mut leanh::LeanObject,
    mut v_inst_2512_: *mut leanh::LeanObject,
    mut v_inst_2513_: *mut leanh::LeanObject,
    mut v_inst_2514_: *mut leanh::LeanObject,
    mut v_p_2515_: *mut leanh::LeanObject,
    mut v_acc_2516_: *mut leanh::LeanObject,
    mut v_a_2517_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2518_: *mut leanh::LeanObject = core::ptr::null_mut();
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
    leanh::lean_dec_ref(v_inst_2513_);
    return v_res_2518_;
}
pub unsafe fn l_Std_Internal_Parsec_manyChars___redArg(
    mut v_inst_2519_: *mut leanh::LeanObject,
    mut v_inst_2520_: *mut leanh::LeanObject,
    mut v_p_2521_: *mut leanh::LeanObject,
    mut v_a_2522_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2523_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2524_: *mut leanh::LeanObject = core::ptr::null_mut();
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
    mut v_00_u03b9_2525_: *mut leanh::LeanObject,
    mut v_elem_2526_: *mut leanh::LeanObject,
    mut v_idx_2527_: *mut leanh::LeanObject,
    mut v_inst_2528_: *mut leanh::LeanObject,
    mut v_inst_2529_: *mut leanh::LeanObject,
    mut v_inst_2530_: *mut leanh::LeanObject,
    mut v_p_2531_: *mut leanh::LeanObject,
    mut v_a_2532_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2533_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2534_: *mut leanh::LeanObject = core::ptr::null_mut();
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
    mut v_00_u03b9_2535_: *mut leanh::LeanObject,
    mut v_elem_2536_: *mut leanh::LeanObject,
    mut v_idx_2537_: *mut leanh::LeanObject,
    mut v_inst_2538_: *mut leanh::LeanObject,
    mut v_inst_2539_: *mut leanh::LeanObject,
    mut v_inst_2540_: *mut leanh::LeanObject,
    mut v_p_2541_: *mut leanh::LeanObject,
    mut v_a_2542_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2543_: *mut leanh::LeanObject = core::ptr::null_mut();
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
    leanh::lean_dec_ref(v_inst_2539_);
    return v_res_2543_;
}
pub unsafe fn l_Std_Internal_Parsec_many1Chars___redArg(
    mut v_inst_2544_: *mut leanh::LeanObject,
    mut v_inst_2545_: *mut leanh::LeanObject,
    mut v_p_2546_: *mut leanh::LeanObject,
    mut v_a_2547_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2548_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_pos_2549_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_res_2550_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2551_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2552_: u32 = 0;
    let mut v___x_2553_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2554_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_pos_2555_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_err_2556_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2558_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2559_: u8 = 0;
    let mut v___x_2561_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2562_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2563_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                leanh::lean_inc_ref(v_p_2546_);
                v___x_2548_ = leanh::lean_apply_1(v_p_2546_, v_a_2547_);
                if leanh::lean_obj_tag(v___x_2548_) == 0 {
                    v_pos_2549_ = leanh::lean_ctor_get(v___x_2548_, 0);
                    leanh::lean_inc(v_pos_2549_);
                    v_res_2550_ = leanh::lean_ctor_get(v___x_2548_, 1);
                    leanh::lean_inc(v_res_2550_);
                    leanh::lean_dec_ref_known(v___x_2548_, 2);
                    v___x_2551_ = l_Std_Internal_Parsec_instInhabited___lam__0___closed__0;
                    v___x_2552_ = leanh::lean_unbox_uint32(v_res_2550_);
                    leanh::lean_dec(v_res_2550_);
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
                    leanh::lean_dec_ref(v_p_2546_);
                    leanh::lean_dec_ref(v_inst_2545_);
                    leanh::lean_dec_ref(v_inst_2544_);
                    v_pos_2555_ = leanh::lean_ctor_get(v___x_2548_, 0);
                    v_err_2556_ = leanh::lean_ctor_get(v___x_2548_, 1);
                    v_isSharedCheck_2563_ = (!leanh::lean_is_exclusive(v___x_2548_)) as u8;
                    if v_isSharedCheck_2563_ == 0 {
                        v___x_2558_ = v___x_2548_;
                        v_isShared_2559_ = v_isSharedCheck_2563_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_err_2556_);
                        leanh::lean_inc(v_pos_2555_);
                        leanh::lean_dec(v___x_2548_);
                        v___x_2558_ = leanh::lean_box(0);
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
                    v_reuseFailAlloc_2562_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2562_, 0, v_pos_2555_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2562_, 1, v_err_2556_);
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
    mut v_00_u03b9_2564_: *mut leanh::LeanObject,
    mut v_elem_2565_: *mut leanh::LeanObject,
    mut v_idx_2566_: *mut leanh::LeanObject,
    mut v_inst_2567_: *mut leanh::LeanObject,
    mut v_inst_2568_: *mut leanh::LeanObject,
    mut v_inst_2569_: *mut leanh::LeanObject,
    mut v_p_2570_: *mut leanh::LeanObject,
    mut v_a_2571_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2572_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_pos_2573_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_res_2574_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2575_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2576_: u32 = 0;
    let mut v___x_2577_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2578_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_pos_2579_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_err_2580_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2582_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2583_: u8 = 0;
    let mut v___x_2585_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2586_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2587_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                leanh::lean_inc_ref(v_p_2570_);
                v___x_2572_ = leanh::lean_apply_1(v_p_2570_, v_a_2571_);
                if leanh::lean_obj_tag(v___x_2572_) == 0 {
                    v_pos_2573_ = leanh::lean_ctor_get(v___x_2572_, 0);
                    leanh::lean_inc(v_pos_2573_);
                    v_res_2574_ = leanh::lean_ctor_get(v___x_2572_, 1);
                    leanh::lean_inc(v_res_2574_);
                    leanh::lean_dec_ref_known(v___x_2572_, 2);
                    v___x_2575_ = l_Std_Internal_Parsec_instInhabited___lam__0___closed__0;
                    v___x_2576_ = leanh::lean_unbox_uint32(v_res_2574_);
                    leanh::lean_dec(v_res_2574_);
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
                    leanh::lean_dec_ref(v_p_2570_);
                    leanh::lean_dec_ref(v_inst_2569_);
                    leanh::lean_dec_ref(v_inst_2567_);
                    v_pos_2579_ = leanh::lean_ctor_get(v___x_2572_, 0);
                    v_err_2580_ = leanh::lean_ctor_get(v___x_2572_, 1);
                    v_isSharedCheck_2587_ = (!leanh::lean_is_exclusive(v___x_2572_)) as u8;
                    if v_isSharedCheck_2587_ == 0 {
                        v___x_2582_ = v___x_2572_;
                        v_isShared_2583_ = v_isSharedCheck_2587_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_err_2580_);
                        leanh::lean_inc(v_pos_2579_);
                        leanh::lean_dec(v___x_2572_);
                        v___x_2582_ = leanh::lean_box(0);
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
                    v_reuseFailAlloc_2586_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2586_, 0, v_pos_2579_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2586_, 1, v_err_2580_);
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
    mut v_00_u03b9_2588_: *mut leanh::LeanObject,
    mut v_elem_2589_: *mut leanh::LeanObject,
    mut v_idx_2590_: *mut leanh::LeanObject,
    mut v_inst_2591_: *mut leanh::LeanObject,
    mut v_inst_2592_: *mut leanh::LeanObject,
    mut v_inst_2593_: *mut leanh::LeanObject,
    mut v_p_2594_: *mut leanh::LeanObject,
    mut v_a_2595_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2596_: *mut leanh::LeanObject = core::ptr::null_mut();
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
    leanh::lean_dec_ref(v_inst_2592_);
    return v_res_2596_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Std_Internal_Parsec_Basic(
    builtin: u8,
) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Init_NotationExtra(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_ToString_Macro(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Array_Basic(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Std_Internal_Parsec_Basic(
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
pub unsafe fn initialize_Std_Internal_Parsec_Basic(builtin: u8) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Init_NotationExtra(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Init_Data_ToString_Macro(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Init_Data_Array_Basic(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Std_Internal_Parsec_Basic(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = meta_initialize_Std_Internal_Parsec_Basic(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return initialize_Std_Internal_Parsec_Basic(builtin);
}