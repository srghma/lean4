// Lean compiler output
// Module: Init.Data.ToString.Basic
// Imports: Init.Data.Repr Init.Data.Char.Basic
use crate::r#gen::Init::Data::Char::Basic::{
    initialize_Init_Data_Char_Basic, runtime_initialize_Init_Data_Char_Basic,
};
use crate::r#gen::Init::Data::Format::Basic::{l_Std_Format_defWidth, l_Std_Format_pretty};
use crate::r#gen::Init::Data::Repr::{
    initialize_Init_Data_Repr, l_Nat_reprFast, l_Repr_addAppParen,
    runtime_initialize_Init_Data_Repr,
};
use crate::r#gen::Init::Data::String::Bootstrap::l_Substring_Raw_Internal_toString___boxed;
use crate::lean_imports_rs::Init::Data::String::Bootstrap::{
    lean_string_any, lean_string_append, lean_string_isprefixof, lean_string_push,
};
use crate::lean_imports_rs::Init::Data::UInt::BasicAux::{
    lean_uint8_to_nat, lean_uint16_to_nat, lean_uint64_to_nat, lean_usize_to_nat,
};
use crate::lean_imports_rs::Init::Prelude::{lean_uint32_dec_eq, lean_uint32_to_nat};
pub static l_instToStringString___closed__0_value: crate::leanh::LeanClosureObject<0> =
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
        m_fun: l_instToStringString___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_instToStringString___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_instToStringString___closed__0_value) as *mut crate::leanh::LeanObject;
pub static mut l_instToStringString: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_instToStringString___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_instToStringRaw___closed__0_value: crate::leanh::LeanClosureObject<0> =
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
        m_fun: l_Substring_Raw_Internal_toString___boxed as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_instToStringRaw___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_instToStringRaw___closed__0_value) as *mut crate::leanh::LeanObject;
pub static mut l_instToStringRaw: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_instToStringRaw___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_instToStringChar___lam__0___closed__0_value: crate::leanh::LeanStringObject<1> =
    crate::leanh::LeanStringObject {
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
static mut l_instToStringChar___lam__0___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_instToStringChar___lam__0___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_instToStringChar___closed__0_value: crate::leanh::LeanClosureObject<0> =
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
        m_fun: l_instToStringChar___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_instToStringChar___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_instToStringChar___closed__0_value) as *mut crate::leanh::LeanObject;
pub static mut l_instToStringChar: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_instToStringChar___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_instToStringBool___lam__0___closed__0_value: crate::leanh::LeanStringObject<6> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 6,
        m_capacity: 6,
        m_length: 5,
        m_data: [102, 97, 108, 115, 101, 0],
    };
static mut l_instToStringBool___lam__0___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_instToStringBool___lam__0___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_instToStringBool___lam__0___closed__1_value: crate::leanh::LeanStringObject<5> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 5,
        m_capacity: 5,
        m_length: 4,
        m_data: [116, 114, 117, 101, 0],
    };
static mut l_instToStringBool___lam__0___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_instToStringBool___lam__0___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_instToStringBool___closed__0_value: crate::leanh::LeanClosureObject<0> =
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
        m_fun: l_instToStringBool___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_instToStringBool___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_instToStringBool___closed__0_value) as *mut crate::leanh::LeanObject;
pub static mut l_instToStringBool: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_instToStringBool___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_instToStringDecidable___closed__0_value: crate::leanh::LeanClosureObject<0> =
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
        m_fun: l_instToStringDecidable___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_instToStringDecidable___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_instToStringDecidable___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_instToStringPUnit___lam__0___closed__0_value: crate::leanh::LeanStringObject<3> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 3,
        m_capacity: 3,
        m_length: 2,
        m_data: [40, 41, 0],
    };
static mut l_instToStringPUnit___lam__0___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_instToStringPUnit___lam__0___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_instToStringPUnit___closed__0_value: crate::leanh::LeanClosureObject<0> =
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
        m_fun: l_instToStringPUnit___lam__0 as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_instToStringPUnit___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_instToStringPUnit___closed__0_value) as *mut crate::leanh::LeanObject;
pub static mut l_instToStringPUnit: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_instToStringPUnit___closed__0_value) as *mut crate::leanh::LeanObject;
pub static mut l_instToStringUnit: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_instToStringPUnit___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_instToStringNat___closed__0_value: crate::leanh::LeanClosureObject<0> =
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
        m_fun: l_Nat_reprFast as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_instToStringNat___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_instToStringNat___closed__0_value) as *mut crate::leanh::LeanObject;
pub static mut l_instToStringNat: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_instToStringNat___closed__0_value) as *mut crate::leanh::LeanObject;
pub static mut l_instToStringRaw__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_instToStringNat___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_instToStringUInt8___closed__0_value: crate::leanh::LeanClosureObject<0> =
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
        m_fun: l_instToStringUInt8___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_instToStringUInt8___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_instToStringUInt8___closed__0_value) as *mut crate::leanh::LeanObject;
pub static mut l_instToStringUInt8: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_instToStringUInt8___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_instToStringUInt16___closed__0_value: crate::leanh::LeanClosureObject<0> =
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
        m_fun: l_instToStringUInt16___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_instToStringUInt16___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_instToStringUInt16___closed__0_value) as *mut crate::leanh::LeanObject;
pub static mut l_instToStringUInt16: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_instToStringUInt16___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_instToStringUInt32___closed__0_value: crate::leanh::LeanClosureObject<0> =
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
        m_fun: l_instToStringUInt32___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_instToStringUInt32___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_instToStringUInt32___closed__0_value) as *mut crate::leanh::LeanObject;
pub static mut l_instToStringUInt32: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_instToStringUInt32___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_instToStringUInt64___closed__0_value: crate::leanh::LeanClosureObject<0> =
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
        m_fun: l_instToStringUInt64___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_instToStringUInt64___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_instToStringUInt64___closed__0_value) as *mut crate::leanh::LeanObject;
pub static mut l_instToStringUInt64: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_instToStringUInt64___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_instToStringUSize___closed__0_value: crate::leanh::LeanClosureObject<0> =
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
        m_fun: l_instToStringUSize___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_instToStringUSize___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_instToStringUSize___closed__0_value) as *mut crate::leanh::LeanObject;
pub static mut l_instToStringUSize: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_instToStringUSize___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_instToStringFormat___closed__0_value: crate::leanh::LeanClosureObject<0> =
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
        m_fun: l_instToStringFormat___lam__0 as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_instToStringFormat___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_instToStringFormat___closed__0_value) as *mut crate::leanh::LeanObject;
pub static mut l_instToStringFormat: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_instToStringFormat___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_addParenHeuristic___closed__0_value: crate::leanh::LeanClosureObject<0> =
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
        m_fun: l_addParenHeuristic___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_addParenHeuristic___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_addParenHeuristic___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_addParenHeuristic___closed__1_value: crate::leanh::LeanStringObject<2> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 2,
        m_capacity: 2,
        m_length: 1,
        m_data: [40, 0],
    };
static mut l_addParenHeuristic___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_addParenHeuristic___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l_addParenHeuristic___closed__2_value: crate::leanh::LeanStringObject<2> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 2,
        m_capacity: 2,
        m_length: 1,
        m_data: [123, 0],
    };
static mut l_addParenHeuristic___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_addParenHeuristic___closed__2_value) as *mut crate::leanh::LeanObject;
pub static l_addParenHeuristic___closed__3_value: crate::leanh::LeanStringObject<3> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 3,
        m_capacity: 3,
        m_length: 2,
        m_data: [35, 91, 0],
    };
static mut l_addParenHeuristic___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_addParenHeuristic___closed__3_value) as *mut crate::leanh::LeanObject;
pub static l_addParenHeuristic___closed__4_value: crate::leanh::LeanStringObject<2> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 2,
        m_capacity: 2,
        m_length: 1,
        m_data: [41, 0],
    };
static mut l_addParenHeuristic___closed__4: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_addParenHeuristic___closed__4_value) as *mut crate::leanh::LeanObject;
pub static l_addParenHeuristic___closed__5_value: crate::leanh::LeanStringObject<2> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 2,
        m_capacity: 2,
        m_length: 1,
        m_data: [91, 0],
    };
static mut l_addParenHeuristic___closed__5: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_addParenHeuristic___closed__5_value) as *mut crate::leanh::LeanObject;
pub static l_instToStringOption___redArg___lam__0___closed__0_value:
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
    m_data: [110, 111, 110, 101, 0],
};
static mut l_instToStringOption___redArg___lam__0___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_instToStringOption___redArg___lam__0___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_instToStringOption___redArg___lam__0___closed__1_value:
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
    m_data: [40, 115, 111, 109, 101, 32, 0],
};
static mut l_instToStringOption___redArg___lam__0___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_instToStringOption___redArg___lam__0___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_instToStringSum___redArg___lam__0___closed__0_value: crate::leanh::LeanStringObject<
    6,
> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 6,
    m_capacity: 6,
    m_length: 5,
    m_data: [40, 105, 110, 108, 32, 0],
};
static mut l_instToStringSum___redArg___lam__0___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_instToStringSum___redArg___lam__0___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_instToStringSum___redArg___lam__0___closed__1_value: crate::leanh::LeanStringObject<
    6,
> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 6,
    m_capacity: 6,
    m_length: 5,
    m_data: [40, 105, 110, 114, 32, 0],
};
static mut l_instToStringSum___redArg___lam__0___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_instToStringSum___redArg___lam__0___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_instToStringProd___redArg___lam__0___closed__0_value: crate::leanh::LeanStringObject<
    3,
> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 3,
    m_capacity: 3,
    m_length: 2,
    m_data: [44, 32, 0],
};
static mut l_instToStringProd___redArg___lam__0___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_instToStringProd___redArg___lam__0___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_instToStringSigma___redArg___lam__0___closed__0_value: crate::leanh::LeanStringObject<
    4,
> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 4,
    m_capacity: 4,
    m_length: 1,
    m_data: [226, 159, 168, 0],
};
static mut l_instToStringSigma___redArg___lam__0___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_instToStringSigma___redArg___lam__0___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_instToStringSigma___redArg___lam__0___closed__1_value: crate::leanh::LeanStringObject<
    4,
> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 4,
    m_capacity: 4,
    m_length: 1,
    m_data: [226, 159, 169, 0],
};
static mut l_instToStringSigma___redArg___lam__0___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_instToStringSigma___redArg___lam__0___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_instToStringExcept___redArg___lam__0___closed__0_value:
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
    m_data: [101, 114, 114, 111, 114, 58, 32, 0],
};
static mut l_instToStringExcept___redArg___lam__0___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_instToStringExcept___redArg___lam__0___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_instToStringExcept___redArg___lam__0___closed__1_value:
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
    m_data: [111, 107, 58, 32, 0],
};
static mut l_instToStringExcept___redArg___lam__0___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_instToStringExcept___redArg___lam__0___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_instReprExcept___redArg___lam__0___closed__0_value: crate::leanh::LeanStringObject<
    14,
> = crate::leanh::LeanStringObject {
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
        69, 120, 99, 101, 112, 116, 46, 101, 114, 114, 111, 114, 32, 0,
    ],
};
static mut l_instReprExcept___redArg___lam__0___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_instReprExcept___redArg___lam__0___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_instReprExcept___redArg___lam__0___closed__1_value: crate::leanh::LeanCtorObject<1> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 3,
        },
        m_objs: [
            core::ptr::addr_of!(l_instReprExcept___redArg___lam__0___closed__0_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_instReprExcept___redArg___lam__0___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_instReprExcept___redArg___lam__0___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_instReprExcept___redArg___lam__0___closed__2_value: crate::leanh::LeanStringObject<
    11,
> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 11,
    m_capacity: 11,
    m_length: 10,
    m_data: [69, 120, 99, 101, 112, 116, 46, 111, 107, 32, 0],
};
static mut l_instReprExcept___redArg___lam__0___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_instReprExcept___redArg___lam__0___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l_instReprExcept___redArg___lam__0___closed__3_value: crate::leanh::LeanCtorObject<1> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 3,
        },
        m_objs: [
            core::ptr::addr_of!(l_instReprExcept___redArg___lam__0___closed__2_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_instReprExcept___redArg___lam__0___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_instReprExcept___redArg___lam__0___closed__3_value)
        as *mut crate::leanh::LeanObject;
pub unsafe fn l_instToStringId___aux__1___redArg(
    mut v_inst_328_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc_ref(v_inst_328_);
    return v_inst_328_;
}
pub unsafe fn l_instToStringId___aux__1___redArg___boxed(
    mut v_inst_329_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_330_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_330_ = l_instToStringId___aux__1___redArg(v_inst_329_);
    crate::leanh::lean_dec_ref(v_inst_329_);
    return v_res_330_;
}
pub unsafe fn l_instToStringId___aux__1(
    mut v_00_u03b1_331_: *mut crate::leanh::LeanObject,
    mut v_inst_332_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc_ref(v_inst_332_);
    return v_inst_332_;
}
pub unsafe fn l_instToStringId___aux__1___boxed(
    mut v_00_u03b1_333_: *mut crate::leanh::LeanObject,
    mut v_inst_334_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_335_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_335_ = l_instToStringId___aux__1(v_00_u03b1_333_, v_inst_334_);
    crate::leanh::lean_dec_ref(v_inst_334_);
    return v_res_335_;
}
pub unsafe fn l_instToStringId___redArg(
    mut v_inst_336_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc_ref(v_inst_336_);
    return v_inst_336_;
}
pub unsafe fn l_instToStringId___redArg___boxed(
    mut v_inst_337_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_338_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_338_ = l_instToStringId___redArg(v_inst_337_);
    crate::leanh::lean_dec_ref(v_inst_337_);
    return v_res_338_;
}
pub unsafe fn l_instToStringId(
    mut v_00_u03b1_339_: *mut crate::leanh::LeanObject,
    mut v_inst_340_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc_ref(v_inst_340_);
    return v_inst_340_;
}
pub unsafe fn l_instToStringId___boxed(
    mut v_00_u03b1_341_: *mut crate::leanh::LeanObject,
    mut v_inst_342_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_343_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_343_ = l_instToStringId(v_00_u03b1_341_, v_inst_342_);
    crate::leanh::lean_dec_ref(v_inst_342_);
    return v_res_343_;
}
pub unsafe fn l_instToStringId__1___aux__1___redArg(
    mut v_inst_344_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc_ref(v_inst_344_);
    return v_inst_344_;
}
pub unsafe fn l_instToStringId__1___aux__1___redArg___boxed(
    mut v_inst_345_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_346_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_346_ = l_instToStringId__1___aux__1___redArg(v_inst_345_);
    crate::leanh::lean_dec_ref(v_inst_345_);
    return v_res_346_;
}
pub unsafe fn l_instToStringId__1___aux__1(
    mut v_00_u03b1_347_: *mut crate::leanh::LeanObject,
    mut v_inst_348_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc_ref(v_inst_348_);
    return v_inst_348_;
}
pub unsafe fn l_instToStringId__1___aux__1___boxed(
    mut v_00_u03b1_349_: *mut crate::leanh::LeanObject,
    mut v_inst_350_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_351_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_351_ = l_instToStringId__1___aux__1(v_00_u03b1_349_, v_inst_350_);
    crate::leanh::lean_dec_ref(v_inst_350_);
    return v_res_351_;
}
pub unsafe fn l_instToStringId__1___redArg(
    mut v_inst_352_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc_ref(v_inst_352_);
    return v_inst_352_;
}
pub unsafe fn l_instToStringId__1___redArg___boxed(
    mut v_inst_353_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_354_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_354_ = l_instToStringId__1___redArg(v_inst_353_);
    crate::leanh::lean_dec_ref(v_inst_353_);
    return v_res_354_;
}
pub unsafe fn l_instToStringId__1(
    mut v_00_u03b1_355_: *mut crate::leanh::LeanObject,
    mut v_inst_356_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc_ref(v_inst_356_);
    return v_inst_356_;
}
pub unsafe fn l_instToStringId__1___boxed(
    mut v_00_u03b1_357_: *mut crate::leanh::LeanObject,
    mut v_inst_358_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_359_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_359_ = l_instToStringId__1(v_00_u03b1_357_, v_inst_358_);
    crate::leanh::lean_dec_ref(v_inst_358_);
    return v_res_359_;
}
pub unsafe fn l_instToStringString___lam__0(
    mut v_s_360_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc_ref(v_s_360_);
    return v_s_360_;
}
pub unsafe fn l_instToStringString___lam__0___boxed(
    mut v_s_361_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_362_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_362_ = l_instToStringString___lam__0(v_s_361_);
    crate::leanh::lean_dec_ref(v_s_361_);
    return v_res_362_;
}
pub unsafe fn l_instToStringChar___lam__0(mut v_c_368_: u32) -> *mut crate::leanh::LeanObject {
    let mut v___x_369_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_370_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_369_ = l_instToStringChar___lam__0___closed__0;
    v___x_370_ = lean_string_push(v___x_369_, v_c_368_);
    return v___x_370_;
}
pub unsafe fn l_instToStringChar___lam__0___boxed(
    mut v_c_371_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_c_boxed_372_: u32 = 0;
    let mut v_res_373_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_c_boxed_372_ = crate::leanh::lean_unbox_uint32(v_c_371_);
    crate::leanh::lean_dec(v_c_371_);
    v_res_373_ = l_instToStringChar___lam__0(v_c_boxed_372_);
    return v_res_373_;
}
pub unsafe fn l_instToStringBool___lam__0(mut v_b_378_: u8) -> *mut crate::leanh::LeanObject {
    if v_b_378_ == 0 {
        let mut v___x_379_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_379_ = l_instToStringBool___lam__0___closed__0;
        return v___x_379_;
    } else {
        let mut v___x_380_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_380_ = l_instToStringBool___lam__0___closed__1;
        return v___x_380_;
    }
}
pub unsafe fn l_instToStringBool___lam__0___boxed(
    mut v_b_381_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_b_boxed_382_: u8 = 0;
    let mut v_res_383_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_b_boxed_382_ = (crate::leanh::lean_unbox(v_b_381_) as u8);
    v_res_383_ = l_instToStringBool___lam__0(v_b_boxed_382_);
    return v_res_383_;
}
pub unsafe fn l_instToStringDecidable___lam__0(mut v_h_386_: u8) -> *mut crate::leanh::LeanObject {
    if v_h_386_ == 0 {
        let mut v___x_387_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_387_ = l_instToStringBool___lam__0___closed__0;
        return v___x_387_;
    } else {
        let mut v___x_388_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_388_ = l_instToStringBool___lam__0___closed__1;
        return v___x_388_;
    }
}
pub unsafe fn l_instToStringDecidable___lam__0___boxed(
    mut v_h_389_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_h_boxed_390_: u8 = 0;
    let mut v_res_391_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_h_boxed_390_ = (crate::leanh::lean_unbox(v_h_389_) as u8);
    v_res_391_ = l_instToStringDecidable___lam__0(v_h_boxed_390_);
    return v_res_391_;
}
pub unsafe fn l_instToStringDecidable(
    mut v_p_393_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_394_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_394_ = l_instToStringDecidable___closed__0;
    return v___f_394_;
}
pub unsafe fn l_instToStringPUnit___lam__0(
    mut v_x_396_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_397_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_397_ = l_instToStringPUnit___lam__0___closed__0;
    return v___x_397_;
}
pub unsafe fn l_instToStringULift___redArg___lam__0(
    mut v_inst_400_: *mut crate::leanh::LeanObject,
    mut v_v_401_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_402_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_402_ = crate::leanh::lean_apply_1(v_inst_400_, v_v_401_);
    return v___x_402_;
}
pub unsafe fn l_instToStringULift___redArg(
    mut v_inst_403_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_404_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_404_ = crate::leanh::lean_alloc_closure(
        l_instToStringULift___redArg___lam__0 as *mut core::ffi::c_void,
        2,
        1,
    );
    crate::leanh::lean_closure_set(v___f_404_, 0, v_inst_403_);
    return v___f_404_;
}
pub unsafe fn l_instToStringULift(
    mut v_00_u03b1_405_: *mut crate::leanh::LeanObject,
    mut v_inst_406_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_407_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_407_ = crate::leanh::lean_alloc_closure(
        l_instToStringULift___redArg___lam__0 as *mut core::ffi::c_void,
        2,
        1,
    );
    crate::leanh::lean_closure_set(v___f_407_, 0, v_inst_406_);
    return v___f_407_;
}
pub unsafe fn l_instToStringFin(
    mut v_n_412_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_413_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_413_ = l_instToStringNat___closed__0;
    return v___f_413_;
}
pub unsafe fn l_instToStringFin___boxed(
    mut v_n_414_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_415_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_415_ = l_instToStringFin(v_n_414_);
    crate::leanh::lean_dec(v_n_414_);
    return v_res_415_;
}
pub unsafe fn l_instToStringUInt8___lam__0(mut v_n_416_: u8) -> *mut crate::leanh::LeanObject {
    let mut v___x_417_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_418_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_417_ = lean_uint8_to_nat(v_n_416_);
    v___x_418_ = l_Nat_reprFast(v___x_417_);
    return v___x_418_;
}
pub unsafe fn l_instToStringUInt8___lam__0___boxed(
    mut v_n_419_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_n_boxed_420_: u8 = 0;
    let mut v_res_421_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_n_boxed_420_ = (crate::leanh::lean_unbox(v_n_419_) as u8);
    v_res_421_ = l_instToStringUInt8___lam__0(v_n_boxed_420_);
    return v_res_421_;
}
pub unsafe fn l_instToStringUInt16___lam__0(mut v_n_424_: u16) -> *mut crate::leanh::LeanObject {
    let mut v___x_425_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_426_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_425_ = lean_uint16_to_nat(v_n_424_);
    v___x_426_ = l_Nat_reprFast(v___x_425_);
    return v___x_426_;
}
pub unsafe fn l_instToStringUInt16___lam__0___boxed(
    mut v_n_427_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_n_boxed_428_: u16 = 0;
    let mut v_res_429_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_n_boxed_428_ = (crate::leanh::lean_unbox(v_n_427_) as u16);
    v_res_429_ = l_instToStringUInt16___lam__0(v_n_boxed_428_);
    return v_res_429_;
}
pub unsafe fn l_instToStringUInt32___lam__0(mut v_n_432_: u32) -> *mut crate::leanh::LeanObject {
    let mut v___x_433_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_434_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_433_ = lean_uint32_to_nat(v_n_432_);
    v___x_434_ = l_Nat_reprFast(v___x_433_);
    return v___x_434_;
}
pub unsafe fn l_instToStringUInt32___lam__0___boxed(
    mut v_n_435_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_n_boxed_436_: u32 = 0;
    let mut v_res_437_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_n_boxed_436_ = crate::leanh::lean_unbox_uint32(v_n_435_);
    crate::leanh::lean_dec(v_n_435_);
    v_res_437_ = l_instToStringUInt32___lam__0(v_n_boxed_436_);
    return v_res_437_;
}
pub unsafe fn l_instToStringUInt64___lam__0(mut v_n_440_: u64) -> *mut crate::leanh::LeanObject {
    let mut v___x_441_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_442_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_441_ = lean_uint64_to_nat(v_n_440_);
    v___x_442_ = l_Nat_reprFast(v___x_441_);
    return v___x_442_;
}
pub unsafe fn l_instToStringUInt64___lam__0___boxed(
    mut v_n_443_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_n_boxed_444_: u64 = 0;
    let mut v_res_445_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_n_boxed_444_ = crate::leanh::lean_unbox_uint64(v_n_443_);
    crate::leanh::lean_dec_ref(v_n_443_);
    v_res_445_ = l_instToStringUInt64___lam__0(v_n_boxed_444_);
    return v_res_445_;
}
pub unsafe fn l_instToStringUSize___lam__0(mut v_n_448_: usize) -> *mut crate::leanh::LeanObject {
    let mut v___x_449_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_450_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_449_ = lean_usize_to_nat(v_n_448_);
    v___x_450_ = l_Nat_reprFast(v___x_449_);
    return v___x_450_;
}
pub unsafe fn l_instToStringUSize___lam__0___boxed(
    mut v_n_451_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_n_boxed_452_: usize = 0;
    let mut v_res_453_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_n_boxed_452_ = crate::leanh::lean_unbox_usize(v_n_451_);
    crate::leanh::lean_dec(v_n_451_);
    v_res_453_ = l_instToStringUSize___lam__0(v_n_boxed_452_);
    return v_res_453_;
}
pub unsafe fn l_instToStringFormat___lam__0(
    mut v_f_456_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_457_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_458_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_459_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_457_ = l_Std_Format_defWidth;
    v___x_458_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_459_ = l_Std_Format_pretty(v_f_456_, v___x_457_, v___x_458_, v___x_458_);
    return v___x_459_;
}
pub unsafe fn l_addParenHeuristic___lam__0(mut v___y_462_: u32) -> u8 {
    let mut v___y_464_: u8 = 0;
    let mut v___x_465_: u32 = 0;
    let mut v___x_466_: u8 = 0;
    let mut v___x_467_: u32 = 0;
    let mut v___x_468_: u8 = 0;
    let mut v___x_469_: u32 = 0;
    let mut v___x_470_: u8 = 0;
    let mut v___x_471_: u32 = 0;
    let mut v___x_472_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_469_ = 32;
                v___x_470_ = lean_uint32_dec_eq(v___y_462_, v___x_469_);
                if v___x_470_ == 0 {
                    v___x_471_ = 9;
                    v___x_472_ = lean_uint32_dec_eq(v___y_462_, v___x_471_);
                    v___y_464_ = v___x_472_;
                    state = 1;
                    continue;
                } else {
                    v___y_464_ = v___x_470_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                if v___y_464_ == 0 {
                    v___x_465_ = 13;
                    v___x_466_ = lean_uint32_dec_eq(v___y_462_, v___x_465_);
                    if v___x_466_ == 0 {
                        v___x_467_ = 10;
                        v___x_468_ = lean_uint32_dec_eq(v___y_462_, v___x_467_);
                        return v___x_468_;
                    } else {
                        return v___x_466_;
                    }
                } else {
                    return v___y_464_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_addParenHeuristic___lam__0___boxed(
    mut v___y_473_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___y_211__boxed_474_: u32 = 0;
    let mut v_res_475_: u8 = 0;
    let mut v_r_476_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___y_211__boxed_474_ = crate::leanh::lean_unbox_uint32(v___y_473_);
    crate::leanh::lean_dec(v___y_473_);
    v_res_475_ = l_addParenHeuristic___lam__0(v___y_211__boxed_474_);
    v_r_476_ = crate::leanh::lean_box((v_res_475_) as usize);
    return v_r_476_;
}
pub unsafe fn l_addParenHeuristic(
    mut v_s_483_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_484_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_485_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_487_: u8 = 0;
    let mut v___x_488_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_489_: u8 = 0;
    let mut v___x_490_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_491_: u8 = 0;
    let mut v___x_492_: u8 = 0;
    let mut v___x_493_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_494_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_495_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_496_: u8 = 0;
    let mut v___x_497_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_498_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___f_484_ = l_addParenHeuristic___closed__0;
                v___x_485_ = l_addParenHeuristic___closed__1;
                crate::leanh::lean_inc_ref(v_s_483_);
                v___x_496_ = lean_string_isprefixof(v___x_485_, v_s_483_);
                if v___x_496_ == 0 {
                    v___x_497_ = l_addParenHeuristic___closed__5;
                    crate::leanh::lean_inc_ref(v_s_483_);
                    v___x_498_ = lean_string_isprefixof(v___x_497_, v_s_483_);
                    v___y_487_ = v___x_498_;
                    state = 1;
                    continue;
                } else {
                    v___y_487_ = v___x_496_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                if v___y_487_ == 0 {
                    v___x_488_ = l_addParenHeuristic___closed__2;
                    crate::leanh::lean_inc_ref(v_s_483_);
                    v___x_489_ = lean_string_isprefixof(v___x_488_, v_s_483_);
                    if v___x_489_ == 0 {
                        v___x_490_ = l_addParenHeuristic___closed__3;
                        crate::leanh::lean_inc_ref(v_s_483_);
                        v___x_491_ = lean_string_isprefixof(v___x_490_, v_s_483_);
                        if v___x_491_ == 0 {
                            crate::leanh::lean_inc_ref(v_s_483_);
                            v___x_492_ = lean_string_any(v_s_483_, v___f_484_);
                            if v___x_492_ == 0 {
                                return v_s_483_;
                            } else {
                                v___x_493_ = lean_string_append(v___x_485_, v_s_483_);
                                crate::leanh::lean_dec_ref(v_s_483_);
                                v___x_494_ = l_addParenHeuristic___closed__4;
                                v___x_495_ = lean_string_append(v___x_493_, v___x_494_);
                                return v___x_495_;
                            }
                        } else {
                            return v_s_483_;
                        }
                    } else {
                        return v_s_483_;
                    }
                } else {
                    return v_s_483_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_instToStringOption___redArg___lam__0(
    mut v_inst_501_: *mut crate::leanh::LeanObject,
    mut v_x_502_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_502_) == 0 {
        let mut v___x_503_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec_ref(v_inst_501_);
        v___x_503_ = l_instToStringOption___redArg___lam__0___closed__0;
        return v___x_503_;
    } else {
        let mut v_val_504_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_505_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_506_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_507_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_508_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_509_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_510_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_val_504_ = crate::leanh::lean_ctor_get(v_x_502_, 0);
        crate::leanh::lean_inc(v_val_504_);
        crate::leanh::lean_dec_ref_known(v_x_502_, 1);
        v___x_505_ = l_instToStringOption___redArg___lam__0___closed__1;
        v___x_506_ = crate::leanh::lean_apply_1(v_inst_501_, v_val_504_);
        v___x_507_ = l_addParenHeuristic(v___x_506_);
        v___x_508_ = lean_string_append(v___x_505_, v___x_507_);
        crate::leanh::lean_dec_ref(v___x_507_);
        v___x_509_ = l_addParenHeuristic___closed__4;
        v___x_510_ = lean_string_append(v___x_508_, v___x_509_);
        return v___x_510_;
    }
}
pub unsafe fn l_instToStringOption___redArg(
    mut v_inst_511_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_512_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_512_ = crate::leanh::lean_alloc_closure(
        l_instToStringOption___redArg___lam__0 as *mut core::ffi::c_void,
        2,
        1,
    );
    crate::leanh::lean_closure_set(v___f_512_, 0, v_inst_511_);
    return v___f_512_;
}
pub unsafe fn l_instToStringOption(
    mut v_00_u03b1_513_: *mut crate::leanh::LeanObject,
    mut v_inst_514_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_515_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_515_ = crate::leanh::lean_alloc_closure(
        l_instToStringOption___redArg___lam__0 as *mut core::ffi::c_void,
        2,
        1,
    );
    crate::leanh::lean_closure_set(v___f_515_, 0, v_inst_514_);
    return v___f_515_;
}
pub unsafe fn l_instToStringSum___redArg___lam__0(
    mut v_inst_518_: *mut crate::leanh::LeanObject,
    mut v_inst_519_: *mut crate::leanh::LeanObject,
    mut v_x_520_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_520_) == 0 {
        let mut v_val_521_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_522_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_523_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_524_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_525_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_526_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_527_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec_ref(v_inst_519_);
        v_val_521_ = crate::leanh::lean_ctor_get(v_x_520_, 0);
        crate::leanh::lean_inc(v_val_521_);
        crate::leanh::lean_dec_ref_known(v_x_520_, 1);
        v___x_522_ = l_instToStringSum___redArg___lam__0___closed__0;
        v___x_523_ = crate::leanh::lean_apply_1(v_inst_518_, v_val_521_);
        v___x_524_ = l_addParenHeuristic(v___x_523_);
        v___x_525_ = lean_string_append(v___x_522_, v___x_524_);
        crate::leanh::lean_dec_ref(v___x_524_);
        v___x_526_ = l_addParenHeuristic___closed__4;
        v___x_527_ = lean_string_append(v___x_525_, v___x_526_);
        return v___x_527_;
    } else {
        let mut v_val_528_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_529_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_530_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_531_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_532_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_533_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_534_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec_ref(v_inst_518_);
        v_val_528_ = crate::leanh::lean_ctor_get(v_x_520_, 0);
        crate::leanh::lean_inc(v_val_528_);
        crate::leanh::lean_dec_ref_known(v_x_520_, 1);
        v___x_529_ = l_instToStringSum___redArg___lam__0___closed__1;
        v___x_530_ = crate::leanh::lean_apply_1(v_inst_519_, v_val_528_);
        v___x_531_ = l_addParenHeuristic(v___x_530_);
        v___x_532_ = lean_string_append(v___x_529_, v___x_531_);
        crate::leanh::lean_dec_ref(v___x_531_);
        v___x_533_ = l_addParenHeuristic___closed__4;
        v___x_534_ = lean_string_append(v___x_532_, v___x_533_);
        return v___x_534_;
    }
}
pub unsafe fn l_instToStringSum___redArg(
    mut v_inst_535_: *mut crate::leanh::LeanObject,
    mut v_inst_536_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_537_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_537_ = crate::leanh::lean_alloc_closure(
        l_instToStringSum___redArg___lam__0 as *mut core::ffi::c_void,
        3,
        2,
    );
    crate::leanh::lean_closure_set(v___f_537_, 0, v_inst_535_);
    crate::leanh::lean_closure_set(v___f_537_, 1, v_inst_536_);
    return v___f_537_;
}
pub unsafe fn l_instToStringSum(
    mut v_00_u03b1_538_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_539_: *mut crate::leanh::LeanObject,
    mut v_inst_540_: *mut crate::leanh::LeanObject,
    mut v_inst_541_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_542_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_542_ = crate::leanh::lean_alloc_closure(
        l_instToStringSum___redArg___lam__0 as *mut core::ffi::c_void,
        3,
        2,
    );
    crate::leanh::lean_closure_set(v___f_542_, 0, v_inst_540_);
    crate::leanh::lean_closure_set(v___f_542_, 1, v_inst_541_);
    return v___f_542_;
}
pub unsafe fn l_instToStringProd___redArg___lam__0(
    mut v_inst_544_: *mut crate::leanh::LeanObject,
    mut v_inst_545_: *mut crate::leanh::LeanObject,
    mut v_x_546_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_fst_547_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_548_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_549_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_550_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_551_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_552_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_553_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_554_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_555_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_556_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_557_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_fst_547_ = crate::leanh::lean_ctor_get(v_x_546_, 0);
    crate::leanh::lean_inc(v_fst_547_);
    v_snd_548_ = crate::leanh::lean_ctor_get(v_x_546_, 1);
    crate::leanh::lean_inc(v_snd_548_);
    crate::leanh::lean_dec_ref(v_x_546_);
    v___x_549_ = l_addParenHeuristic___closed__1;
    v___x_550_ = crate::leanh::lean_apply_1(v_inst_544_, v_fst_547_);
    v___x_551_ = lean_string_append(v___x_549_, v___x_550_);
    crate::leanh::lean_dec_ref(v___x_550_);
    v___x_552_ = l_instToStringProd___redArg___lam__0___closed__0;
    v___x_553_ = lean_string_append(v___x_551_, v___x_552_);
    v___x_554_ = crate::leanh::lean_apply_1(v_inst_545_, v_snd_548_);
    v___x_555_ = lean_string_append(v___x_553_, v___x_554_);
    crate::leanh::lean_dec_ref(v___x_554_);
    v___x_556_ = l_addParenHeuristic___closed__4;
    v___x_557_ = lean_string_append(v___x_555_, v___x_556_);
    return v___x_557_;
}
pub unsafe fn l_instToStringProd___redArg(
    mut v_inst_558_: *mut crate::leanh::LeanObject,
    mut v_inst_559_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_560_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_560_ = crate::leanh::lean_alloc_closure(
        l_instToStringProd___redArg___lam__0 as *mut core::ffi::c_void,
        3,
        2,
    );
    crate::leanh::lean_closure_set(v___f_560_, 0, v_inst_558_);
    crate::leanh::lean_closure_set(v___f_560_, 1, v_inst_559_);
    return v___f_560_;
}
pub unsafe fn l_instToStringProd(
    mut v_00_u03b1_561_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_562_: *mut crate::leanh::LeanObject,
    mut v_inst_563_: *mut crate::leanh::LeanObject,
    mut v_inst_564_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_565_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_565_ = crate::leanh::lean_alloc_closure(
        l_instToStringProd___redArg___lam__0 as *mut core::ffi::c_void,
        3,
        2,
    );
    crate::leanh::lean_closure_set(v___f_565_, 0, v_inst_563_);
    crate::leanh::lean_closure_set(v___f_565_, 1, v_inst_564_);
    return v___f_565_;
}
pub unsafe fn l_instToStringSigma___redArg___lam__0(
    mut v_inst_568_: *mut crate::leanh::LeanObject,
    mut v_inst_569_: *mut crate::leanh::LeanObject,
    mut v_x_570_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_fst_571_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_572_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_573_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_574_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_575_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_576_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_577_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_578_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_579_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_580_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_581_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_fst_571_ = crate::leanh::lean_ctor_get(v_x_570_, 0);
    crate::leanh::lean_inc_n(v_fst_571_, 2);
    v_snd_572_ = crate::leanh::lean_ctor_get(v_x_570_, 1);
    crate::leanh::lean_inc(v_snd_572_);
    crate::leanh::lean_dec_ref(v_x_570_);
    v___x_573_ = l_instToStringSigma___redArg___lam__0___closed__0;
    v___x_574_ = crate::leanh::lean_apply_1(v_inst_568_, v_fst_571_);
    v___x_575_ = lean_string_append(v___x_573_, v___x_574_);
    crate::leanh::lean_dec_ref(v___x_574_);
    v___x_576_ = l_instToStringProd___redArg___lam__0___closed__0;
    v___x_577_ = lean_string_append(v___x_575_, v___x_576_);
    v___x_578_ = crate::leanh::lean_apply_2(v_inst_569_, v_fst_571_, v_snd_572_);
    v___x_579_ = lean_string_append(v___x_577_, v___x_578_);
    crate::leanh::lean_dec_ref(v___x_578_);
    v___x_580_ = l_instToStringSigma___redArg___lam__0___closed__1;
    v___x_581_ = lean_string_append(v___x_579_, v___x_580_);
    return v___x_581_;
}
pub unsafe fn l_instToStringSigma___redArg(
    mut v_inst_582_: *mut crate::leanh::LeanObject,
    mut v_inst_583_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_584_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_584_ = crate::leanh::lean_alloc_closure(
        l_instToStringSigma___redArg___lam__0 as *mut core::ffi::c_void,
        3,
        2,
    );
    crate::leanh::lean_closure_set(v___f_584_, 0, v_inst_582_);
    crate::leanh::lean_closure_set(v___f_584_, 1, v_inst_583_);
    return v___f_584_;
}
pub unsafe fn l_instToStringSigma(
    mut v_00_u03b1_585_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_586_: *mut crate::leanh::LeanObject,
    mut v_inst_587_: *mut crate::leanh::LeanObject,
    mut v_inst_588_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_589_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_589_ = crate::leanh::lean_alloc_closure(
        l_instToStringSigma___redArg___lam__0 as *mut core::ffi::c_void,
        3,
        2,
    );
    crate::leanh::lean_closure_set(v___f_589_, 0, v_inst_587_);
    crate::leanh::lean_closure_set(v___f_589_, 1, v_inst_588_);
    return v___f_589_;
}
pub unsafe fn l_instToStringSubtype___redArg___lam__0(
    mut v_inst_590_: *mut crate::leanh::LeanObject,
    mut v_s_591_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_592_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_592_ = crate::leanh::lean_apply_1(v_inst_590_, v_s_591_);
    return v___x_592_;
}
pub unsafe fn l_instToStringSubtype___redArg(
    mut v_inst_593_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_594_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_594_ = crate::leanh::lean_alloc_closure(
        l_instToStringSubtype___redArg___lam__0 as *mut core::ffi::c_void,
        2,
        1,
    );
    crate::leanh::lean_closure_set(v___f_594_, 0, v_inst_593_);
    return v___f_594_;
}
pub unsafe fn l_instToStringSubtype(
    mut v_00_u03b1_595_: *mut crate::leanh::LeanObject,
    mut v_p_596_: *mut crate::leanh::LeanObject,
    mut v_inst_597_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_598_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_598_ = crate::leanh::lean_alloc_closure(
        l_instToStringSubtype___redArg___lam__0 as *mut core::ffi::c_void,
        2,
        1,
    );
    crate::leanh::lean_closure_set(v___f_598_, 0, v_inst_597_);
    return v___f_598_;
}
pub unsafe fn l_instToStringExcept___redArg___lam__0(
    mut v_inst_601_: *mut crate::leanh::LeanObject,
    mut v_inst_602_: *mut crate::leanh::LeanObject,
    mut v_x_603_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_603_) == 0 {
        let mut v_a_604_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_605_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_606_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_607_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec_ref(v_inst_602_);
        v_a_604_ = crate::leanh::lean_ctor_get(v_x_603_, 0);
        crate::leanh::lean_inc(v_a_604_);
        crate::leanh::lean_dec_ref_known(v_x_603_, 1);
        v___x_605_ = l_instToStringExcept___redArg___lam__0___closed__0;
        v___x_606_ = crate::leanh::lean_apply_1(v_inst_601_, v_a_604_);
        v___x_607_ = lean_string_append(v___x_605_, v___x_606_);
        crate::leanh::lean_dec_ref(v___x_606_);
        return v___x_607_;
    } else {
        let mut v_a_608_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_609_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_610_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_611_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec_ref(v_inst_601_);
        v_a_608_ = crate::leanh::lean_ctor_get(v_x_603_, 0);
        crate::leanh::lean_inc(v_a_608_);
        crate::leanh::lean_dec_ref_known(v_x_603_, 1);
        v___x_609_ = l_instToStringExcept___redArg___lam__0___closed__1;
        v___x_610_ = crate::leanh::lean_apply_1(v_inst_602_, v_a_608_);
        v___x_611_ = lean_string_append(v___x_609_, v___x_610_);
        crate::leanh::lean_dec_ref(v___x_610_);
        return v___x_611_;
    }
}
pub unsafe fn l_instToStringExcept___redArg(
    mut v_inst_612_: *mut crate::leanh::LeanObject,
    mut v_inst_613_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_614_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_614_ = crate::leanh::lean_alloc_closure(
        l_instToStringExcept___redArg___lam__0 as *mut core::ffi::c_void,
        3,
        2,
    );
    crate::leanh::lean_closure_set(v___f_614_, 0, v_inst_612_);
    crate::leanh::lean_closure_set(v___f_614_, 1, v_inst_613_);
    return v___f_614_;
}
pub unsafe fn l_instToStringExcept(
    mut v_00_u03b5_615_: *mut crate::leanh::LeanObject,
    mut v_00_u03b1_616_: *mut crate::leanh::LeanObject,
    mut v_inst_617_: *mut crate::leanh::LeanObject,
    mut v_inst_618_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_619_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_619_ = crate::leanh::lean_alloc_closure(
        l_instToStringExcept___redArg___lam__0 as *mut core::ffi::c_void,
        3,
        2,
    );
    crate::leanh::lean_closure_set(v___f_619_, 0, v_inst_617_);
    crate::leanh::lean_closure_set(v___f_619_, 1, v_inst_618_);
    return v___f_619_;
}
pub unsafe fn l_instReprExcept___redArg___lam__0(
    mut v_inst_626_: *mut crate::leanh::LeanObject,
    mut v_inst_627_: *mut crate::leanh::LeanObject,
    mut v_x_628_: *mut crate::leanh::LeanObject,
    mut v_x_629_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_628_) == 0 {
        let mut v_a_630_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_631_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_632_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_633_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_634_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_635_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec_ref(v_inst_627_);
        v_a_630_ = crate::leanh::lean_ctor_get(v_x_628_, 0);
        crate::leanh::lean_inc(v_a_630_);
        crate::leanh::lean_dec_ref_known(v_x_628_, 1);
        v___x_631_ = l_instReprExcept___redArg___lam__0___closed__1;
        v___x_632_ = crate::leanh::lean_unsigned_to_nat(1024);
        v___x_633_ = crate::leanh::lean_apply_2(v_inst_626_, v_a_630_, v___x_632_);
        v___x_634_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_634_, 0, v___x_631_);
        crate::leanh::lean_ctor_set(v___x_634_, 1, v___x_633_);
        v___x_635_ = l_Repr_addAppParen(v___x_634_, v_x_629_);
        return v___x_635_;
    } else {
        let mut v_a_636_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_637_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_638_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_639_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_640_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_641_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec_ref(v_inst_626_);
        v_a_636_ = crate::leanh::lean_ctor_get(v_x_628_, 0);
        crate::leanh::lean_inc(v_a_636_);
        crate::leanh::lean_dec_ref_known(v_x_628_, 1);
        v___x_637_ = l_instReprExcept___redArg___lam__0___closed__3;
        v___x_638_ = crate::leanh::lean_unsigned_to_nat(1024);
        v___x_639_ = crate::leanh::lean_apply_2(v_inst_627_, v_a_636_, v___x_638_);
        v___x_640_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_640_, 0, v___x_637_);
        crate::leanh::lean_ctor_set(v___x_640_, 1, v___x_639_);
        v___x_641_ = l_Repr_addAppParen(v___x_640_, v_x_629_);
        return v___x_641_;
    }
}
pub unsafe fn l_instReprExcept___redArg___lam__0___boxed(
    mut v_inst_642_: *mut crate::leanh::LeanObject,
    mut v_inst_643_: *mut crate::leanh::LeanObject,
    mut v_x_644_: *mut crate::leanh::LeanObject,
    mut v_x_645_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_646_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_646_ = l_instReprExcept___redArg___lam__0(v_inst_642_, v_inst_643_, v_x_644_, v_x_645_);
    crate::leanh::lean_dec(v_x_645_);
    return v_res_646_;
}
pub unsafe fn l_instReprExcept___redArg(
    mut v_inst_647_: *mut crate::leanh::LeanObject,
    mut v_inst_648_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_649_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_649_ = crate::leanh::lean_alloc_closure(
        l_instReprExcept___redArg___lam__0___boxed as *mut core::ffi::c_void,
        4,
        2,
    );
    crate::leanh::lean_closure_set(v___f_649_, 0, v_inst_647_);
    crate::leanh::lean_closure_set(v___f_649_, 1, v_inst_648_);
    return v___f_649_;
}
pub unsafe fn l_instReprExcept(
    mut v_00_u03b5_650_: *mut crate::leanh::LeanObject,
    mut v_00_u03b1_651_: *mut crate::leanh::LeanObject,
    mut v_inst_652_: *mut crate::leanh::LeanObject,
    mut v_inst_653_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_654_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_654_ = crate::leanh::lean_alloc_closure(
        l_instReprExcept___redArg___lam__0___boxed as *mut core::ffi::c_void,
        4,
        2,
    );
    crate::leanh::lean_closure_set(v___f_654_, 0, v_inst_652_);
    crate::leanh::lean_closure_set(v___f_654_, 1, v_inst_653_);
    return v___f_654_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Init_Data_ToString_Basic(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Init_Data_Repr(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Char_Basic(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Init_Data_ToString_Basic(
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
pub unsafe fn initialize_Init_Data_ToString_Basic(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Init_Data_Repr(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Data_Char_Basic(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_ToString_Basic(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Init_Data_ToString_Basic(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Init_Data_ToString_Basic(builtin);
}
