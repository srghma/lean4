// Lean compiler output
// Module: Lean.DocString.Types
// Imports: Init.Data.Ord Init.Data.Nat.Compare Init.Data.Array.GetLit
use crate::r#gen::Init::Data::Array::Basic::{
    l_Array_append___redArg, l_Array_isEqvAux___redArg, l_Array_repr___redArg,
};
use crate::r#gen::Init::Data::Array::GetLit::{
    initialize_Init_Data_Array_GetLit, runtime_initialize_Init_Data_Array_GetLit,
};
use crate::r#gen::Init::Data::Int::Repr::l_Int_repr;
use crate::r#gen::Init::Data::Nat::Compare::{
    initialize_Init_Data_Nat_Compare, runtime_initialize_Init_Data_Nat_Compare,
};
use crate::r#gen::Init::Data::Option::Basic::l_Option_instBEq_beq___redArg;
use crate::r#gen::Init::Data::Ord::Array::l_Array_compareLex___redArg;
use crate::r#gen::Init::Data::Ord::{initialize_Init_Data_Ord, runtime_initialize_Init_Data_Ord};
use crate::r#gen::Init::Data::Repr::{l_Option_repr___redArg, l_Repr_addAppParen, l_String_quote};
use crate::ffi::{
    lean_int_dec_eq, lean_int_dec_lt, lean_nat_to_int,
};
use crate::ffi::lean_string_compare;
use crate::ffi::lean_string_length;
use crate::ffi::{
    lean_array_get_size, lean_array_push, lean_mk_empty_array_with_capacity, lean_nat_dec_eq,
    lean_nat_dec_le, lean_nat_dec_lt, lean_string_dec_eq,
};
pub static l_Lean_Doc_instReprMathMode_repr___closed__0_value: crate::leanh::LeanStringObject<25> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 25,
        m_capacity: 25,
        m_length: 24,
        m_data: [
            76, 101, 97, 110, 46, 68, 111, 99, 46, 77, 97, 116, 104, 77, 111, 100, 101, 46, 105,
            110, 108, 105, 110, 101, 0,
        ],
    };
static mut l_Lean_Doc_instReprMathMode_repr___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Doc_instReprMathMode_repr___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Doc_instReprMathMode_repr___closed__1_value: crate::leanh::LeanCtorObject<1> =
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
            core::ptr::addr_of!(l_Lean_Doc_instReprMathMode_repr___closed__0_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Doc_instReprMathMode_repr___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Doc_instReprMathMode_repr___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Doc_instReprMathMode_repr___closed__2_value: crate::leanh::LeanStringObject<26> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 26,
        m_capacity: 26,
        m_length: 25,
        m_data: [
            76, 101, 97, 110, 46, 68, 111, 99, 46, 77, 97, 116, 104, 77, 111, 100, 101, 46, 100,
            105, 115, 112, 108, 97, 121, 0,
        ],
    };
static mut l_Lean_Doc_instReprMathMode_repr___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Doc_instReprMathMode_repr___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Doc_instReprMathMode_repr___closed__3_value: crate::leanh::LeanCtorObject<1> =
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
            core::ptr::addr_of!(l_Lean_Doc_instReprMathMode_repr___closed__2_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Doc_instReprMathMode_repr___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Doc_instReprMathMode_repr___closed__3_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Doc_instReprMathMode_repr___closed__4_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Doc_instReprMathMode_repr___closed__4: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Doc_instReprMathMode_repr___closed__5_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Doc_instReprMathMode_repr___closed__5: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Doc_instReprMathMode___closed__0_value: crate::leanh::LeanClosureObject<0> =
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
        m_fun: l_Lean_Doc_instReprMathMode_repr___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_Doc_instReprMathMode___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Doc_instReprMathMode___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Lean_Doc_instReprMathMode: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Doc_instReprMathMode___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Doc_instBEqMathMode___closed__0_value: crate::leanh::LeanClosureObject<0> =
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
        m_fun: l_Lean_Doc_instBEqMathMode_beq___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_Doc_instBEqMathMode___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Doc_instBEqMathMode___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Lean_Doc_instBEqMathMode: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Doc_instBEqMathMode___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Doc_instHashableMathMode___closed__0_value: crate::leanh::LeanClosureObject<0> =
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
        m_fun: l_Lean_Doc_instHashableMathMode_hash___boxed as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_Doc_instHashableMathMode___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Doc_instHashableMathMode___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Lean_Doc_instHashableMathMode: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Doc_instHashableMathMode___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Doc_instOrdMathMode___closed__0_value: crate::leanh::LeanClosureObject<0> =
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
        m_fun: l_Lean_Doc_instOrdMathMode_ord___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_Doc_instOrdMathMode___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Doc_instOrdMathMode___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Lean_Doc_instOrdMathMode: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Doc_instOrdMathMode___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Doc_instReprInline_repr___redArg___closed__0_value:
    crate::leanh::LeanStringObject<21> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 21,
    m_capacity: 21,
    m_length: 20,
    m_data: [
        76, 101, 97, 110, 46, 68, 111, 99, 46, 73, 110, 108, 105, 110, 101, 46, 116, 101, 120, 116,
        0,
    ],
};
static mut l_Lean_Doc_instReprInline_repr___redArg___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Doc_instReprInline_repr___redArg___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Doc_instReprInline_repr___redArg___closed__1_value: crate::leanh::LeanCtorObject<
    1,
> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Doc_instReprInline_repr___redArg___closed__0_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Doc_instReprInline_repr___redArg___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Doc_instReprInline_repr___redArg___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Doc_instReprInline_repr___redArg___closed__2_value: crate::leanh::LeanCtorObject<
    2,
> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 5,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Doc_instReprInline_repr___redArg___closed__1_value)
            as *mut crate::leanh::LeanObject,
        (((1 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Doc_instReprInline_repr___redArg___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Doc_instReprInline_repr___redArg___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Doc_instReprInline_repr___redArg___closed__3_value:
    crate::leanh::LeanStringObject<21> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 21,
    m_capacity: 21,
    m_length: 20,
    m_data: [
        76, 101, 97, 110, 46, 68, 111, 99, 46, 73, 110, 108, 105, 110, 101, 46, 101, 109, 112, 104,
        0,
    ],
};
static mut l_Lean_Doc_instReprInline_repr___redArg___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Doc_instReprInline_repr___redArg___closed__3_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Doc_instReprInline_repr___redArg___closed__4_value: crate::leanh::LeanCtorObject<
    1,
> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Doc_instReprInline_repr___redArg___closed__3_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Doc_instReprInline_repr___redArg___closed__4: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Doc_instReprInline_repr___redArg___closed__4_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Doc_instReprInline_repr___redArg___closed__5_value: crate::leanh::LeanCtorObject<
    2,
> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 5,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Doc_instReprInline_repr___redArg___closed__4_value)
            as *mut crate::leanh::LeanObject,
        (((1 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Doc_instReprInline_repr___redArg___closed__5: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Doc_instReprInline_repr___redArg___closed__5_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Doc_instReprInline_repr___redArg___closed__6_value:
    crate::leanh::LeanStringObject<21> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 21,
    m_capacity: 21,
    m_length: 20,
    m_data: [
        76, 101, 97, 110, 46, 68, 111, 99, 46, 73, 110, 108, 105, 110, 101, 46, 98, 111, 108, 100,
        0,
    ],
};
static mut l_Lean_Doc_instReprInline_repr___redArg___closed__6: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Doc_instReprInline_repr___redArg___closed__6_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Doc_instReprInline_repr___redArg___closed__7_value: crate::leanh::LeanCtorObject<
    1,
> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Doc_instReprInline_repr___redArg___closed__6_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Doc_instReprInline_repr___redArg___closed__7: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Doc_instReprInline_repr___redArg___closed__7_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Doc_instReprInline_repr___redArg___closed__8_value: crate::leanh::LeanCtorObject<
    2,
> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 5,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Doc_instReprInline_repr___redArg___closed__7_value)
            as *mut crate::leanh::LeanObject,
        (((1 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Doc_instReprInline_repr___redArg___closed__8: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Doc_instReprInline_repr___redArg___closed__8_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Doc_instReprInline_repr___redArg___closed__9_value:
    crate::leanh::LeanStringObject<21> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 21,
    m_capacity: 21,
    m_length: 20,
    m_data: [
        76, 101, 97, 110, 46, 68, 111, 99, 46, 73, 110, 108, 105, 110, 101, 46, 99, 111, 100, 101,
        0,
    ],
};
static mut l_Lean_Doc_instReprInline_repr___redArg___closed__9: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Doc_instReprInline_repr___redArg___closed__9_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Doc_instReprInline_repr___redArg___closed__10_value:
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
        core::ptr::addr_of!(l_Lean_Doc_instReprInline_repr___redArg___closed__9_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Doc_instReprInline_repr___redArg___closed__10: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Doc_instReprInline_repr___redArg___closed__10_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Doc_instReprInline_repr___redArg___closed__11_value:
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
        core::ptr::addr_of!(l_Lean_Doc_instReprInline_repr___redArg___closed__10_value)
            as *mut crate::leanh::LeanObject,
        (((1 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Doc_instReprInline_repr___redArg___closed__11: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Doc_instReprInline_repr___redArg___closed__11_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Doc_instReprInline_repr___redArg___closed__12_value:
    crate::leanh::LeanStringObject<21> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 21,
    m_capacity: 21,
    m_length: 20,
    m_data: [
        76, 101, 97, 110, 46, 68, 111, 99, 46, 73, 110, 108, 105, 110, 101, 46, 109, 97, 116, 104,
        0,
    ],
};
static mut l_Lean_Doc_instReprInline_repr___redArg___closed__12: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Doc_instReprInline_repr___redArg___closed__12_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Doc_instReprInline_repr___redArg___closed__13_value:
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
        core::ptr::addr_of!(l_Lean_Doc_instReprInline_repr___redArg___closed__12_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Doc_instReprInline_repr___redArg___closed__13: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Doc_instReprInline_repr___redArg___closed__13_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Doc_instReprInline_repr___redArg___closed__14_value:
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
        core::ptr::addr_of!(l_Lean_Doc_instReprInline_repr___redArg___closed__13_value)
            as *mut crate::leanh::LeanObject,
        (((1 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Doc_instReprInline_repr___redArg___closed__14: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Doc_instReprInline_repr___redArg___closed__14_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Doc_instReprInline_repr___redArg___closed__15_value:
    crate::leanh::LeanStringObject<26> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 26,
    m_capacity: 26,
    m_length: 25,
    m_data: [
        76, 101, 97, 110, 46, 68, 111, 99, 46, 73, 110, 108, 105, 110, 101, 46, 108, 105, 110, 101,
        98, 114, 101, 97, 107, 0,
    ],
};
static mut l_Lean_Doc_instReprInline_repr___redArg___closed__15: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Doc_instReprInline_repr___redArg___closed__15_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Doc_instReprInline_repr___redArg___closed__16_value:
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
        core::ptr::addr_of!(l_Lean_Doc_instReprInline_repr___redArg___closed__15_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Doc_instReprInline_repr___redArg___closed__16: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Doc_instReprInline_repr___redArg___closed__16_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Doc_instReprInline_repr___redArg___closed__17_value:
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
        core::ptr::addr_of!(l_Lean_Doc_instReprInline_repr___redArg___closed__16_value)
            as *mut crate::leanh::LeanObject,
        (((1 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Doc_instReprInline_repr___redArg___closed__17: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Doc_instReprInline_repr___redArg___closed__17_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Doc_instReprInline_repr___redArg___closed__18_value:
    crate::leanh::LeanStringObject<21> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 21,
    m_capacity: 21,
    m_length: 20,
    m_data: [
        76, 101, 97, 110, 46, 68, 111, 99, 46, 73, 110, 108, 105, 110, 101, 46, 108, 105, 110, 107,
        0,
    ],
};
static mut l_Lean_Doc_instReprInline_repr___redArg___closed__18: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Doc_instReprInline_repr___redArg___closed__18_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Doc_instReprInline_repr___redArg___closed__19_value:
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
        core::ptr::addr_of!(l_Lean_Doc_instReprInline_repr___redArg___closed__18_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Doc_instReprInline_repr___redArg___closed__19: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Doc_instReprInline_repr___redArg___closed__19_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Doc_instReprInline_repr___redArg___closed__20_value:
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
        core::ptr::addr_of!(l_Lean_Doc_instReprInline_repr___redArg___closed__19_value)
            as *mut crate::leanh::LeanObject,
        (((1 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Doc_instReprInline_repr___redArg___closed__20: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Doc_instReprInline_repr___redArg___closed__20_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Doc_instReprInline_repr___redArg___closed__21_value:
    crate::leanh::LeanStringObject<25> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 25,
    m_capacity: 25,
    m_length: 24,
    m_data: [
        76, 101, 97, 110, 46, 68, 111, 99, 46, 73, 110, 108, 105, 110, 101, 46, 102, 111, 111, 116,
        110, 111, 116, 101, 0,
    ],
};
static mut l_Lean_Doc_instReprInline_repr___redArg___closed__21: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Doc_instReprInline_repr___redArg___closed__21_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Doc_instReprInline_repr___redArg___closed__22_value:
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
        core::ptr::addr_of!(l_Lean_Doc_instReprInline_repr___redArg___closed__21_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Doc_instReprInline_repr___redArg___closed__22: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Doc_instReprInline_repr___redArg___closed__22_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Doc_instReprInline_repr___redArg___closed__23_value:
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
        core::ptr::addr_of!(l_Lean_Doc_instReprInline_repr___redArg___closed__22_value)
            as *mut crate::leanh::LeanObject,
        (((1 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Doc_instReprInline_repr___redArg___closed__23: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Doc_instReprInline_repr___redArg___closed__23_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Doc_instReprInline_repr___redArg___closed__24_value:
    crate::leanh::LeanStringObject<22> = crate::leanh::LeanStringObject {
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
        76, 101, 97, 110, 46, 68, 111, 99, 46, 73, 110, 108, 105, 110, 101, 46, 105, 109, 97, 103,
        101, 0,
    ],
};
static mut l_Lean_Doc_instReprInline_repr___redArg___closed__24: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Doc_instReprInline_repr___redArg___closed__24_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Doc_instReprInline_repr___redArg___closed__25_value:
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
        core::ptr::addr_of!(l_Lean_Doc_instReprInline_repr___redArg___closed__24_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Doc_instReprInline_repr___redArg___closed__25: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Doc_instReprInline_repr___redArg___closed__25_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Doc_instReprInline_repr___redArg___closed__26_value:
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
        core::ptr::addr_of!(l_Lean_Doc_instReprInline_repr___redArg___closed__25_value)
            as *mut crate::leanh::LeanObject,
        (((1 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Doc_instReprInline_repr___redArg___closed__26: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Doc_instReprInline_repr___redArg___closed__26_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Doc_instReprInline_repr___redArg___closed__27_value:
    crate::leanh::LeanStringObject<23> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 23,
    m_capacity: 23,
    m_length: 22,
    m_data: [
        76, 101, 97, 110, 46, 68, 111, 99, 46, 73, 110, 108, 105, 110, 101, 46, 99, 111, 110, 99,
        97, 116, 0,
    ],
};
static mut l_Lean_Doc_instReprInline_repr___redArg___closed__27: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Doc_instReprInline_repr___redArg___closed__27_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Doc_instReprInline_repr___redArg___closed__28_value:
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
        core::ptr::addr_of!(l_Lean_Doc_instReprInline_repr___redArg___closed__27_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Doc_instReprInline_repr___redArg___closed__28: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Doc_instReprInline_repr___redArg___closed__28_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Doc_instReprInline_repr___redArg___closed__29_value:
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
        core::ptr::addr_of!(l_Lean_Doc_instReprInline_repr___redArg___closed__28_value)
            as *mut crate::leanh::LeanObject,
        (((1 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Doc_instReprInline_repr___redArg___closed__29: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Doc_instReprInline_repr___redArg___closed__29_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Doc_instReprInline_repr___redArg___closed__30_value:
    crate::leanh::LeanStringObject<22> = crate::leanh::LeanStringObject {
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
        76, 101, 97, 110, 46, 68, 111, 99, 46, 73, 110, 108, 105, 110, 101, 46, 111, 116, 104, 101,
        114, 0,
    ],
};
static mut l_Lean_Doc_instReprInline_repr___redArg___closed__30: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Doc_instReprInline_repr___redArg___closed__30_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Doc_instReprInline_repr___redArg___closed__31_value:
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
        core::ptr::addr_of!(l_Lean_Doc_instReprInline_repr___redArg___closed__30_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Doc_instReprInline_repr___redArg___closed__31: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Doc_instReprInline_repr___redArg___closed__31_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Doc_instReprInline_repr___redArg___closed__32_value:
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
        core::ptr::addr_of!(l_Lean_Doc_instReprInline_repr___redArg___closed__31_value)
            as *mut crate::leanh::LeanObject,
        (((1 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Doc_instReprInline_repr___redArg___closed__32: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Doc_instReprInline_repr___redArg___closed__32_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Doc_instInhabitedInline_default___closed__0_value:
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
static mut l_Lean_Doc_instInhabitedInline_default___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Doc_instInhabitedInline_default___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Doc_instInhabitedInline_default___closed__1_value: crate::leanh::LeanCtorObject<
    1,
> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 0,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Doc_instInhabitedInline_default___closed__0_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Doc_instInhabitedInline_default___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Doc_instInhabitedInline_default___closed__1_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Doc_instInhabitedInline___closed__0_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Doc_instInhabitedInline___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Doc_instAppendInline___closed__0_value: crate::leanh::LeanClosureObject<0> =
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
        m_fun: l_Lean_Doc_instAppendInline___lam__0 as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_Doc_instAppendInline___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Doc_instAppendInline___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Doc_Inline_empty___closed__0_value: crate::leanh::LeanArrayObject<0> =
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
static mut l_Lean_Doc_Inline_empty___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Doc_Inline_empty___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_Doc_Inline_empty___closed__1_value: crate::leanh::LeanCtorObject<1> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 9,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Doc_Inline_empty___closed__0_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Doc_Inline_empty___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Doc_Inline_empty___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_Doc_instReprListItem_repr___redArg___closed__0_value:
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
static mut l_Lean_Doc_instReprListItem_repr___redArg___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Doc_instReprListItem_repr___redArg___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Doc_instReprListItem_repr___redArg___closed__1_value:
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
    m_data: [99, 111, 110, 116, 101, 110, 116, 115, 0],
};
static mut l_Lean_Doc_instReprListItem_repr___redArg___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Doc_instReprListItem_repr___redArg___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Doc_instReprListItem_repr___redArg___closed__2_value:
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
        core::ptr::addr_of!(l_Lean_Doc_instReprListItem_repr___redArg___closed__1_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Doc_instReprListItem_repr___redArg___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Doc_instReprListItem_repr___redArg___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Doc_instReprListItem_repr___redArg___closed__3_value:
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
        core::ptr::addr_of!(l_Lean_Doc_instReprListItem_repr___redArg___closed__2_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Doc_instReprListItem_repr___redArg___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Doc_instReprListItem_repr___redArg___closed__3_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Doc_instReprListItem_repr___redArg___closed__4_value:
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
static mut l_Lean_Doc_instReprListItem_repr___redArg___closed__4: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Doc_instReprListItem_repr___redArg___closed__4_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Doc_instReprListItem_repr___redArg___closed__5_value:
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
        core::ptr::addr_of!(l_Lean_Doc_instReprListItem_repr___redArg___closed__4_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Doc_instReprListItem_repr___redArg___closed__5: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Doc_instReprListItem_repr___redArg___closed__5_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Doc_instReprListItem_repr___redArg___closed__6_value:
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
        core::ptr::addr_of!(l_Lean_Doc_instReprListItem_repr___redArg___closed__3_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Doc_instReprListItem_repr___redArg___closed__5_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Doc_instReprListItem_repr___redArg___closed__6: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Doc_instReprListItem_repr___redArg___closed__6_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Doc_instReprListItem_repr___redArg___closed__7_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Doc_instReprListItem_repr___redArg___closed__7: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Doc_instReprListItem_repr___redArg___closed__8_value:
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
static mut l_Lean_Doc_instReprListItem_repr___redArg___closed__8: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Doc_instReprListItem_repr___redArg___closed__8_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Doc_instReprListItem_repr___redArg___closed__9_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Doc_instReprListItem_repr___redArg___closed__9: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Doc_instReprListItem_repr___redArg___closed__10_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Doc_instReprListItem_repr___redArg___closed__10: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Doc_instReprListItem_repr___redArg___closed__11_value:
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
        core::ptr::addr_of!(l_Lean_Doc_instReprListItem_repr___redArg___closed__0_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Doc_instReprListItem_repr___redArg___closed__11: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Doc_instReprListItem_repr___redArg___closed__11_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Doc_instReprListItem_repr___redArg___closed__12_value:
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
        core::ptr::addr_of!(l_Lean_Doc_instReprListItem_repr___redArg___closed__8_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Doc_instReprListItem_repr___redArg___closed__12: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Doc_instReprListItem_repr___redArg___closed__12_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Doc_instInhabitedListItem_default___closed__0_value:
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
static mut l_Lean_Doc_instInhabitedListItem_default___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Doc_instInhabitedListItem_default___closed__0_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Doc_instInhabitedListItem___closed__0_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Doc_instInhabitedListItem___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Doc_instReprDescItem_repr___redArg___closed__0_value:
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
    m_data: [116, 101, 114, 109, 0],
};
static mut l_Lean_Doc_instReprDescItem_repr___redArg___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Doc_instReprDescItem_repr___redArg___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Doc_instReprDescItem_repr___redArg___closed__1_value:
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
        core::ptr::addr_of!(l_Lean_Doc_instReprDescItem_repr___redArg___closed__0_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Doc_instReprDescItem_repr___redArg___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Doc_instReprDescItem_repr___redArg___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Doc_instReprDescItem_repr___redArg___closed__2_value:
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
        core::ptr::addr_of!(l_Lean_Doc_instReprDescItem_repr___redArg___closed__1_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Doc_instReprDescItem_repr___redArg___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Doc_instReprDescItem_repr___redArg___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Doc_instReprDescItem_repr___redArg___closed__3_value:
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
        core::ptr::addr_of!(l_Lean_Doc_instReprDescItem_repr___redArg___closed__2_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Doc_instReprListItem_repr___redArg___closed__5_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Doc_instReprDescItem_repr___redArg___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Doc_instReprDescItem_repr___redArg___closed__3_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Doc_instReprDescItem_repr___redArg___closed__4_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Doc_instReprDescItem_repr___redArg___closed__4: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Doc_instReprDescItem_repr___redArg___closed__5_value:
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
static mut l_Lean_Doc_instReprDescItem_repr___redArg___closed__5: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Doc_instReprDescItem_repr___redArg___closed__5_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Doc_instReprDescItem_repr___redArg___closed__6_value:
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
        core::ptr::addr_of!(l_Lean_Doc_instReprDescItem_repr___redArg___closed__5_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Doc_instReprDescItem_repr___redArg___closed__6: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Doc_instReprDescItem_repr___redArg___closed__6_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Doc_instReprDescItem_repr___redArg___closed__7_value:
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
    m_data: [100, 101, 115, 99, 0],
};
static mut l_Lean_Doc_instReprDescItem_repr___redArg___closed__7: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Doc_instReprDescItem_repr___redArg___closed__7_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Doc_instReprDescItem_repr___redArg___closed__8_value:
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
        core::ptr::addr_of!(l_Lean_Doc_instReprDescItem_repr___redArg___closed__7_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Doc_instReprDescItem_repr___redArg___closed__8: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Doc_instReprDescItem_repr___redArg___closed__8_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Doc_instInhabitedDescItem_default___closed__0_value:
    crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 0,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Doc_instInhabitedListItem_default___closed__0_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Doc_instInhabitedListItem_default___closed__0_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Doc_instInhabitedDescItem_default___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Doc_instInhabitedDescItem_default___closed__0_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Doc_instInhabitedDescItem___closed__0_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Doc_instInhabitedDescItem___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Doc_instReprBlock_repr___redArg___closed__0_value:
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
        76, 101, 97, 110, 46, 68, 111, 99, 46, 66, 108, 111, 99, 107, 46, 112, 97, 114, 97, 0,
    ],
};
static mut l_Lean_Doc_instReprBlock_repr___redArg___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Doc_instReprBlock_repr___redArg___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Doc_instReprBlock_repr___redArg___closed__1_value: crate::leanh::LeanCtorObject<
    1,
> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Doc_instReprBlock_repr___redArg___closed__0_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Doc_instReprBlock_repr___redArg___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Doc_instReprBlock_repr___redArg___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Doc_instReprBlock_repr___redArg___closed__2_value: crate::leanh::LeanCtorObject<
    2,
> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 5,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Doc_instReprBlock_repr___redArg___closed__1_value)
            as *mut crate::leanh::LeanObject,
        (((1 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Doc_instReprBlock_repr___redArg___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Doc_instReprBlock_repr___redArg___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Doc_instReprBlock_repr___redArg___closed__3_value:
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
        76, 101, 97, 110, 46, 68, 111, 99, 46, 66, 108, 111, 99, 107, 46, 99, 111, 100, 101, 0,
    ],
};
static mut l_Lean_Doc_instReprBlock_repr___redArg___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Doc_instReprBlock_repr___redArg___closed__3_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Doc_instReprBlock_repr___redArg___closed__4_value: crate::leanh::LeanCtorObject<
    1,
> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Doc_instReprBlock_repr___redArg___closed__3_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Doc_instReprBlock_repr___redArg___closed__4: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Doc_instReprBlock_repr___redArg___closed__4_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Doc_instReprBlock_repr___redArg___closed__5_value: crate::leanh::LeanCtorObject<
    2,
> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 5,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Doc_instReprBlock_repr___redArg___closed__4_value)
            as *mut crate::leanh::LeanObject,
        (((1 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Doc_instReprBlock_repr___redArg___closed__5: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Doc_instReprBlock_repr___redArg___closed__5_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Doc_instReprBlock_repr___redArg___closed__6_value:
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
        76, 101, 97, 110, 46, 68, 111, 99, 46, 66, 108, 111, 99, 107, 46, 117, 108, 0,
    ],
};
static mut l_Lean_Doc_instReprBlock_repr___redArg___closed__6: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Doc_instReprBlock_repr___redArg___closed__6_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Doc_instReprBlock_repr___redArg___closed__7_value: crate::leanh::LeanCtorObject<
    1,
> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Doc_instReprBlock_repr___redArg___closed__6_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Doc_instReprBlock_repr___redArg___closed__7: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Doc_instReprBlock_repr___redArg___closed__7_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Doc_instReprBlock_repr___redArg___closed__8_value: crate::leanh::LeanCtorObject<
    2,
> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 5,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Doc_instReprBlock_repr___redArg___closed__7_value)
            as *mut crate::leanh::LeanObject,
        (((1 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Doc_instReprBlock_repr___redArg___closed__8: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Doc_instReprBlock_repr___redArg___closed__8_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Doc_instReprBlock_repr___redArg___closed__9_value:
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
        76, 101, 97, 110, 46, 68, 111, 99, 46, 66, 108, 111, 99, 107, 46, 111, 108, 0,
    ],
};
static mut l_Lean_Doc_instReprBlock_repr___redArg___closed__9: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Doc_instReprBlock_repr___redArg___closed__9_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Doc_instReprBlock_repr___redArg___closed__10_value: crate::leanh::LeanCtorObject<
    1,
> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Doc_instReprBlock_repr___redArg___closed__9_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Doc_instReprBlock_repr___redArg___closed__10: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Doc_instReprBlock_repr___redArg___closed__10_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Doc_instReprBlock_repr___redArg___closed__11_value: crate::leanh::LeanCtorObject<
    2,
> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 5,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Doc_instReprBlock_repr___redArg___closed__10_value)
            as *mut crate::leanh::LeanObject,
        (((1 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Doc_instReprBlock_repr___redArg___closed__11: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Doc_instReprBlock_repr___redArg___closed__11_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Doc_instReprBlock_repr___redArg___closed__12_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Doc_instReprBlock_repr___redArg___closed__12: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Doc_instReprBlock_repr___redArg___closed__13_value:
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
        76, 101, 97, 110, 46, 68, 111, 99, 46, 66, 108, 111, 99, 107, 46, 100, 108, 0,
    ],
};
static mut l_Lean_Doc_instReprBlock_repr___redArg___closed__13: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Doc_instReprBlock_repr___redArg___closed__13_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Doc_instReprBlock_repr___redArg___closed__14_value: crate::leanh::LeanCtorObject<
    1,
> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Doc_instReprBlock_repr___redArg___closed__13_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Doc_instReprBlock_repr___redArg___closed__14: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Doc_instReprBlock_repr___redArg___closed__14_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Doc_instReprBlock_repr___redArg___closed__15_value: crate::leanh::LeanCtorObject<
    2,
> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 5,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Doc_instReprBlock_repr___redArg___closed__14_value)
            as *mut crate::leanh::LeanObject,
        (((1 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Doc_instReprBlock_repr___redArg___closed__15: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Doc_instReprBlock_repr___redArg___closed__15_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Doc_instReprBlock_repr___redArg___closed__16_value:
    crate::leanh::LeanStringObject<26> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 26,
    m_capacity: 26,
    m_length: 25,
    m_data: [
        76, 101, 97, 110, 46, 68, 111, 99, 46, 66, 108, 111, 99, 107, 46, 98, 108, 111, 99, 107,
        113, 117, 111, 116, 101, 0,
    ],
};
static mut l_Lean_Doc_instReprBlock_repr___redArg___closed__16: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Doc_instReprBlock_repr___redArg___closed__16_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Doc_instReprBlock_repr___redArg___closed__17_value: crate::leanh::LeanCtorObject<
    1,
> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Doc_instReprBlock_repr___redArg___closed__16_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Doc_instReprBlock_repr___redArg___closed__17: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Doc_instReprBlock_repr___redArg___closed__17_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Doc_instReprBlock_repr___redArg___closed__18_value: crate::leanh::LeanCtorObject<
    2,
> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 5,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Doc_instReprBlock_repr___redArg___closed__17_value)
            as *mut crate::leanh::LeanObject,
        (((1 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Doc_instReprBlock_repr___redArg___closed__18: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Doc_instReprBlock_repr___redArg___closed__18_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Doc_instReprBlock_repr___redArg___closed__19_value:
    crate::leanh::LeanStringObject<22> = crate::leanh::LeanStringObject {
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
        76, 101, 97, 110, 46, 68, 111, 99, 46, 66, 108, 111, 99, 107, 46, 99, 111, 110, 99, 97,
        116, 0,
    ],
};
static mut l_Lean_Doc_instReprBlock_repr___redArg___closed__19: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Doc_instReprBlock_repr___redArg___closed__19_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Doc_instReprBlock_repr___redArg___closed__20_value: crate::leanh::LeanCtorObject<
    1,
> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Doc_instReprBlock_repr___redArg___closed__19_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Doc_instReprBlock_repr___redArg___closed__20: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Doc_instReprBlock_repr___redArg___closed__20_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Doc_instReprBlock_repr___redArg___closed__21_value: crate::leanh::LeanCtorObject<
    2,
> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 5,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Doc_instReprBlock_repr___redArg___closed__20_value)
            as *mut crate::leanh::LeanObject,
        (((1 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Doc_instReprBlock_repr___redArg___closed__21: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Doc_instReprBlock_repr___redArg___closed__21_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Doc_instReprBlock_repr___redArg___closed__22_value:
    crate::leanh::LeanStringObject<21> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 21,
    m_capacity: 21,
    m_length: 20,
    m_data: [
        76, 101, 97, 110, 46, 68, 111, 99, 46, 66, 108, 111, 99, 107, 46, 111, 116, 104, 101, 114,
        0,
    ],
};
static mut l_Lean_Doc_instReprBlock_repr___redArg___closed__22: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Doc_instReprBlock_repr___redArg___closed__22_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Doc_instReprBlock_repr___redArg___closed__23_value: crate::leanh::LeanCtorObject<
    1,
> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Doc_instReprBlock_repr___redArg___closed__22_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Doc_instReprBlock_repr___redArg___closed__23: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Doc_instReprBlock_repr___redArg___closed__23_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Doc_instReprBlock_repr___redArg___closed__24_value: crate::leanh::LeanCtorObject<
    2,
> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 5,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Doc_instReprBlock_repr___redArg___closed__23_value)
            as *mut crate::leanh::LeanObject,
        (((1 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Doc_instReprBlock_repr___redArg___closed__24: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Doc_instReprBlock_repr___redArg___closed__24_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Doc_instInhabitedBlock_default___closed__0_value: crate::leanh::LeanArrayObject<
    0,
> = crate::leanh::LeanArrayObject {
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
static mut l_Lean_Doc_instInhabitedBlock_default___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Doc_instInhabitedBlock_default___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Doc_instInhabitedBlock_default___closed__1_value: crate::leanh::LeanCtorObject<
    1,
> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 0,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Doc_instInhabitedBlock_default___closed__0_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Doc_instInhabitedBlock_default___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Doc_instInhabitedBlock_default___closed__1_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Doc_instInhabitedBlock___closed__0_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Doc_instInhabitedBlock___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Doc_Block_empty___closed__0_value: crate::leanh::LeanArrayObject<0> =
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
static mut l_Lean_Doc_Block_empty___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Doc_Block_empty___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_Doc_Block_empty___closed__1_value: crate::leanh::LeanCtorObject<1> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 6,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Doc_Block_empty___closed__0_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Doc_Block_empty___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Doc_Block_empty___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_Doc_instReprPart_repr___redArg___closed__0_value: crate::leanh::LeanStringObject<
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
    m_data: [116, 105, 116, 108, 101, 0],
};
static mut l_Lean_Doc_instReprPart_repr___redArg___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Doc_instReprPart_repr___redArg___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Doc_instReprPart_repr___redArg___closed__1_value: crate::leanh::LeanCtorObject<
    1,
> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Doc_instReprPart_repr___redArg___closed__0_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Doc_instReprPart_repr___redArg___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Doc_instReprPart_repr___redArg___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Doc_instReprPart_repr___redArg___closed__2_value: crate::leanh::LeanCtorObject<
    2,
> = crate::leanh::LeanCtorObject {
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
        core::ptr::addr_of!(l_Lean_Doc_instReprPart_repr___redArg___closed__1_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Doc_instReprPart_repr___redArg___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Doc_instReprPart_repr___redArg___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Doc_instReprPart_repr___redArg___closed__3_value: crate::leanh::LeanCtorObject<
    2,
> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 5,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Doc_instReprPart_repr___redArg___closed__2_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Doc_instReprListItem_repr___redArg___closed__5_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Doc_instReprPart_repr___redArg___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Doc_instReprPart_repr___redArg___closed__3_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Doc_instReprPart_repr___redArg___closed__4_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Doc_instReprPart_repr___redArg___closed__4: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Doc_instReprPart_repr___redArg___closed__5_value: crate::leanh::LeanStringObject<
    12,
> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 12,
    m_capacity: 12,
    m_length: 11,
    m_data: [116, 105, 116, 108, 101, 83, 116, 114, 105, 110, 103, 0],
};
static mut l_Lean_Doc_instReprPart_repr___redArg___closed__5: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Doc_instReprPart_repr___redArg___closed__5_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Doc_instReprPart_repr___redArg___closed__6_value: crate::leanh::LeanCtorObject<
    1,
> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Doc_instReprPart_repr___redArg___closed__5_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Doc_instReprPart_repr___redArg___closed__6: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Doc_instReprPart_repr___redArg___closed__6_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Doc_instReprPart_repr___redArg___closed__7_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Doc_instReprPart_repr___redArg___closed__7: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Doc_instReprPart_repr___redArg___closed__8_value: crate::leanh::LeanStringObject<
    9,
> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 9,
    m_capacity: 9,
    m_length: 8,
    m_data: [109, 101, 116, 97, 100, 97, 116, 97, 0],
};
static mut l_Lean_Doc_instReprPart_repr___redArg___closed__8: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Doc_instReprPart_repr___redArg___closed__8_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Doc_instReprPart_repr___redArg___closed__9_value: crate::leanh::LeanCtorObject<
    1,
> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Doc_instReprPart_repr___redArg___closed__8_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Doc_instReprPart_repr___redArg___closed__9: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Doc_instReprPart_repr___redArg___closed__9_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Doc_instReprPart_repr___redArg___closed__10_value:
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
    m_data: [99, 111, 110, 116, 101, 110, 116, 0],
};
static mut l_Lean_Doc_instReprPart_repr___redArg___closed__10: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Doc_instReprPart_repr___redArg___closed__10_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Doc_instReprPart_repr___redArg___closed__11_value: crate::leanh::LeanCtorObject<
    1,
> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Doc_instReprPart_repr___redArg___closed__10_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Doc_instReprPart_repr___redArg___closed__11: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Doc_instReprPart_repr___redArg___closed__11_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Doc_instReprPart_repr___redArg___closed__12_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Doc_instReprPart_repr___redArg___closed__12: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Doc_instReprPart_repr___redArg___closed__13_value:
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
    m_data: [115, 117, 98, 80, 97, 114, 116, 115, 0],
};
static mut l_Lean_Doc_instReprPart_repr___redArg___closed__13: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Doc_instReprPart_repr___redArg___closed__13_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Doc_instReprPart_repr___redArg___closed__14_value: crate::leanh::LeanCtorObject<
    1,
> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Doc_instReprPart_repr___redArg___closed__13_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Doc_instReprPart_repr___redArg___closed__14: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Doc_instReprPart_repr___redArg___closed__14_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Doc_instInhabitedPart_default___closed__0_value: crate::leanh::LeanCtorObject<5> =
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
            core::ptr::addr_of!(l_Lean_Doc_instInhabitedBlock_default___closed__0_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Doc_instInhabitedInline_default___closed__0_value)
                as *mut crate::leanh::LeanObject,
            (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Doc_instInhabitedBlock_default___closed__0_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Doc_instInhabitedBlock_default___closed__0_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Doc_instInhabitedPart_default___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Doc_instInhabitedPart_default___closed__0_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Doc_instInhabitedPart___closed__0_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Doc_instInhabitedPart___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub unsafe fn l_Lean_Doc_MathMode_ctorIdx(mut v_x_2065_: u8) -> *mut crate::leanh::LeanObject {
    if v_x_2065_ == 0 {
        let mut v___x_2066_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_2066_ = crate::leanh::lean_unsigned_to_nat(0);
        return v___x_2066_;
    } else {
        let mut v___x_2067_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_2067_ = crate::leanh::lean_unsigned_to_nat(1);
        return v___x_2067_;
    }
}
pub unsafe fn l_Lean_Doc_MathMode_ctorIdx___boxed(
    mut v_x_2068_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_x_boxed_2069_: u8 = 0;
    let mut v_res_2070_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_x_boxed_2069_ = (crate::leanh::lean_unbox(v_x_2068_) as u8);
    v_res_2070_ = l_Lean_Doc_MathMode_ctorIdx(v_x_boxed_2069_);
    return v_res_2070_;
}
pub unsafe fn l_Lean_Doc_MathMode_toCtorIdx(mut v_x_2071_: u8) -> *mut crate::leanh::LeanObject {
    let mut v___x_2072_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2072_ = l_Lean_Doc_MathMode_ctorIdx(v_x_2071_);
    return v___x_2072_;
}
pub unsafe fn l_Lean_Doc_MathMode_toCtorIdx___boxed(
    mut v_x_2073_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_x_4__boxed_2074_: u8 = 0;
    let mut v_res_2075_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_x_4__boxed_2074_ = (crate::leanh::lean_unbox(v_x_2073_) as u8);
    v_res_2075_ = l_Lean_Doc_MathMode_toCtorIdx(v_x_4__boxed_2074_);
    return v_res_2075_;
}
pub unsafe fn l_Lean_Doc_MathMode_ctorElim___redArg(
    mut v_k_2076_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc(v_k_2076_);
    return v_k_2076_;
}
pub unsafe fn l_Lean_Doc_MathMode_ctorElim___redArg___boxed(
    mut v_k_2077_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2078_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2078_ = l_Lean_Doc_MathMode_ctorElim___redArg(v_k_2077_);
    crate::leanh::lean_dec(v_k_2077_);
    return v_res_2078_;
}
pub unsafe fn l_Lean_Doc_MathMode_ctorElim(
    mut v_motive_2079_: *mut crate::leanh::LeanObject,
    mut v_ctorIdx_2080_: *mut crate::leanh::LeanObject,
    mut v_t_2081_: u8,
    mut v_h_2082_: *mut crate::leanh::LeanObject,
    mut v_k_2083_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc(v_k_2083_);
    return v_k_2083_;
}
pub unsafe fn l_Lean_Doc_MathMode_ctorElim___boxed(
    mut v_motive_2084_: *mut crate::leanh::LeanObject,
    mut v_ctorIdx_2085_: *mut crate::leanh::LeanObject,
    mut v_t_2086_: *mut crate::leanh::LeanObject,
    mut v_h_2087_: *mut crate::leanh::LeanObject,
    mut v_k_2088_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_t_boxed_2089_: u8 = 0;
    let mut v_res_2090_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_t_boxed_2089_ = (crate::leanh::lean_unbox(v_t_2086_) as u8);
    v_res_2090_ = l_Lean_Doc_MathMode_ctorElim(
        v_motive_2084_,
        v_ctorIdx_2085_,
        v_t_boxed_2089_,
        v_h_2087_,
        v_k_2088_,
    );
    crate::leanh::lean_dec(v_k_2088_);
    crate::leanh::lean_dec(v_ctorIdx_2085_);
    return v_res_2090_;
}
pub unsafe fn l_Lean_Doc_MathMode_inline_elim___redArg(
    mut v_inline_2091_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc(v_inline_2091_);
    return v_inline_2091_;
}
pub unsafe fn l_Lean_Doc_MathMode_inline_elim___redArg___boxed(
    mut v_inline_2092_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2093_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2093_ = l_Lean_Doc_MathMode_inline_elim___redArg(v_inline_2092_);
    crate::leanh::lean_dec(v_inline_2092_);
    return v_res_2093_;
}
pub unsafe fn l_Lean_Doc_MathMode_inline_elim(
    mut v_motive_2094_: *mut crate::leanh::LeanObject,
    mut v_t_2095_: u8,
    mut v_h_2096_: *mut crate::leanh::LeanObject,
    mut v_inline_2097_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc(v_inline_2097_);
    return v_inline_2097_;
}
pub unsafe fn l_Lean_Doc_MathMode_inline_elim___boxed(
    mut v_motive_2098_: *mut crate::leanh::LeanObject,
    mut v_t_2099_: *mut crate::leanh::LeanObject,
    mut v_h_2100_: *mut crate::leanh::LeanObject,
    mut v_inline_2101_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_t_boxed_2102_: u8 = 0;
    let mut v_res_2103_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_t_boxed_2102_ = (crate::leanh::lean_unbox(v_t_2099_) as u8);
    v_res_2103_ =
        l_Lean_Doc_MathMode_inline_elim(v_motive_2098_, v_t_boxed_2102_, v_h_2100_, v_inline_2101_);
    crate::leanh::lean_dec(v_inline_2101_);
    return v_res_2103_;
}
pub unsafe fn l_Lean_Doc_MathMode_display_elim___redArg(
    mut v_display_2104_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc(v_display_2104_);
    return v_display_2104_;
}
pub unsafe fn l_Lean_Doc_MathMode_display_elim___redArg___boxed(
    mut v_display_2105_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2106_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2106_ = l_Lean_Doc_MathMode_display_elim___redArg(v_display_2105_);
    crate::leanh::lean_dec(v_display_2105_);
    return v_res_2106_;
}
pub unsafe fn l_Lean_Doc_MathMode_display_elim(
    mut v_motive_2107_: *mut crate::leanh::LeanObject,
    mut v_t_2108_: u8,
    mut v_h_2109_: *mut crate::leanh::LeanObject,
    mut v_display_2110_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc(v_display_2110_);
    return v_display_2110_;
}
pub unsafe fn l_Lean_Doc_MathMode_display_elim___boxed(
    mut v_motive_2111_: *mut crate::leanh::LeanObject,
    mut v_t_2112_: *mut crate::leanh::LeanObject,
    mut v_h_2113_: *mut crate::leanh::LeanObject,
    mut v_display_2114_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_t_boxed_2115_: u8 = 0;
    let mut v_res_2116_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_t_boxed_2115_ = (crate::leanh::lean_unbox(v_t_2112_) as u8);
    v_res_2116_ = l_Lean_Doc_MathMode_display_elim(
        v_motive_2111_,
        v_t_boxed_2115_,
        v_h_2113_,
        v_display_2114_,
    );
    crate::leanh::lean_dec(v_display_2114_);
    return v_res_2116_;
}
pub unsafe fn _init_l_Lean_Doc_instReprMathMode_repr___closed__4() -> *mut crate::leanh::LeanObject
{
    let mut v___x_2123_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2124_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2123_ = crate::leanh::lean_unsigned_to_nat(2);
    v___x_2124_ = lean_nat_to_int(v___x_2123_);
    return v___x_2124_;
}
pub unsafe fn _init_l_Lean_Doc_instReprMathMode_repr___closed__5() -> *mut crate::leanh::LeanObject
{
    let mut v___x_2125_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2126_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2125_ = crate::leanh::lean_unsigned_to_nat(1);
    v___x_2126_ = lean_nat_to_int(v___x_2125_);
    return v___x_2126_;
}
pub unsafe fn l_Lean_Doc_instReprMathMode_repr(
    mut v_x_2127_: u8,
    mut v_prec_2128_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___y_2130_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2131_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2132_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2133_: u8 = 0;
    let mut v___x_2134_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2135_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2137_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2138_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2139_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2140_: u8 = 0;
    let mut v___x_2141_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2142_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2143_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2144_: u8 = 0;
    let mut v___x_2145_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2146_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2147_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2148_: u8 = 0;
    let mut v___x_2149_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2150_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if v_x_2127_ == 0 {
                    v___x_2143_ = crate::leanh::lean_unsigned_to_nat(1024);
                    v___x_2144_ = lean_nat_dec_le(v___x_2143_, v_prec_2128_);
                    if v___x_2144_ == 0 {
                        v___x_2145_ = crate::leanh::lean_obj_once(
                            core::ptr::addr_of_mut!(l_Lean_Doc_instReprMathMode_repr___closed__4),
                            core::ptr::addr_of_mut!(
                                l_Lean_Doc_instReprMathMode_repr___closed__4_once
                            ),
                            _init_l_Lean_Doc_instReprMathMode_repr___closed__4,
                        );
                        v___y_2130_ = v___x_2145_;
                        state = 1;
                        continue;
                    } else {
                        v___x_2146_ = crate::leanh::lean_obj_once(
                            core::ptr::addr_of_mut!(l_Lean_Doc_instReprMathMode_repr___closed__5),
                            core::ptr::addr_of_mut!(
                                l_Lean_Doc_instReprMathMode_repr___closed__5_once
                            ),
                            _init_l_Lean_Doc_instReprMathMode_repr___closed__5,
                        );
                        v___y_2130_ = v___x_2146_;
                        state = 1;
                        continue;
                    }
                } else {
                    v___x_2147_ = crate::leanh::lean_unsigned_to_nat(1024);
                    v___x_2148_ = lean_nat_dec_le(v___x_2147_, v_prec_2128_);
                    if v___x_2148_ == 0 {
                        v___x_2149_ = crate::leanh::lean_obj_once(
                            core::ptr::addr_of_mut!(l_Lean_Doc_instReprMathMode_repr___closed__4),
                            core::ptr::addr_of_mut!(
                                l_Lean_Doc_instReprMathMode_repr___closed__4_once
                            ),
                            _init_l_Lean_Doc_instReprMathMode_repr___closed__4,
                        );
                        v___y_2137_ = v___x_2149_;
                        state = 2;
                        continue;
                    } else {
                        v___x_2150_ = crate::leanh::lean_obj_once(
                            core::ptr::addr_of_mut!(l_Lean_Doc_instReprMathMode_repr___closed__5),
                            core::ptr::addr_of_mut!(
                                l_Lean_Doc_instReprMathMode_repr___closed__5_once
                            ),
                            _init_l_Lean_Doc_instReprMathMode_repr___closed__5,
                        );
                        v___y_2137_ = v___x_2150_;
                        state = 2;
                        continue;
                    }
                }
            }
            1 => {
                v___x_2131_ = l_Lean_Doc_instReprMathMode_repr___closed__1;
                crate::leanh::lean_inc(v___y_2130_);
                v___x_2132_ = crate::leanh::lean_alloc_ctor(4, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2132_, 0, v___y_2130_);
                crate::leanh::lean_ctor_set(v___x_2132_, 1, v___x_2131_);
                v___x_2133_ = 0;
                v___x_2134_ = crate::leanh::lean_alloc_ctor(6, 1, (1) as u32);
                crate::leanh::lean_ctor_set(v___x_2134_, 0, v___x_2132_);
                crate::leanh::lean_ctor_set_uint8(
                    v___x_2134_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                    v___x_2133_,
                );
                v___x_2135_ = l_Repr_addAppParen(v___x_2134_, v_prec_2128_);
                return v___x_2135_;
            }
            2 => {
                v___x_2138_ = l_Lean_Doc_instReprMathMode_repr___closed__3;
                crate::leanh::lean_inc(v___y_2137_);
                v___x_2139_ = crate::leanh::lean_alloc_ctor(4, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2139_, 0, v___y_2137_);
                crate::leanh::lean_ctor_set(v___x_2139_, 1, v___x_2138_);
                v___x_2140_ = 0;
                v___x_2141_ = crate::leanh::lean_alloc_ctor(6, 1, (1) as u32);
                crate::leanh::lean_ctor_set(v___x_2141_, 0, v___x_2139_);
                crate::leanh::lean_ctor_set_uint8(
                    v___x_2141_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                    v___x_2140_,
                );
                v___x_2142_ = l_Repr_addAppParen(v___x_2141_, v_prec_2128_);
                return v___x_2142_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Doc_instReprMathMode_repr___boxed(
    mut v_x_2151_: *mut crate::leanh::LeanObject,
    mut v_prec_2152_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_x_121__boxed_2153_: u8 = 0;
    let mut v_res_2154_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_x_121__boxed_2153_ = (crate::leanh::lean_unbox(v_x_2151_) as u8);
    v_res_2154_ = l_Lean_Doc_instReprMathMode_repr(v_x_121__boxed_2153_, v_prec_2152_);
    crate::leanh::lean_dec(v_prec_2152_);
    return v_res_2154_;
}
pub unsafe fn l_Lean_Doc_instBEqMathMode_beq(mut v_x_2157_: u8, mut v_y_2158_: u8) -> u8 {
    let mut v___x_2159_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2160_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2161_: u8 = 0;
    v___x_2159_ = l_Lean_Doc_MathMode_ctorIdx(v_x_2157_);
    v___x_2160_ = l_Lean_Doc_MathMode_ctorIdx(v_y_2158_);
    v___x_2161_ = lean_nat_dec_eq(v___x_2159_, v___x_2160_);
    crate::leanh::lean_dec(v___x_2160_);
    crate::leanh::lean_dec(v___x_2159_);
    return v___x_2161_;
}
pub unsafe fn l_Lean_Doc_instBEqMathMode_beq___boxed(
    mut v_x_2162_: *mut crate::leanh::LeanObject,
    mut v_y_2163_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_x_17__boxed_2164_: u8 = 0;
    let mut v_y_18__boxed_2165_: u8 = 0;
    let mut v_res_2166_: u8 = 0;
    let mut v_r_2167_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_x_17__boxed_2164_ = (crate::leanh::lean_unbox(v_x_2162_) as u8);
    v_y_18__boxed_2165_ = (crate::leanh::lean_unbox(v_y_2163_) as u8);
    v_res_2166_ = l_Lean_Doc_instBEqMathMode_beq(v_x_17__boxed_2164_, v_y_18__boxed_2165_);
    v_r_2167_ = crate::leanh::lean_box((v_res_2166_) as usize);
    return v_r_2167_;
}
pub unsafe fn l_Lean_Doc_instHashableMathMode_hash(mut v_x_2170_: u8) -> u64 {
    if v_x_2170_ == 0 {
        let mut v___x_2171_: u64 = 0;
        v___x_2171_ = 0u64;
        return v___x_2171_;
    } else {
        let mut v___x_2172_: u64 = 0;
        v___x_2172_ = 1u64;
        return v___x_2172_;
    }
}
pub unsafe fn l_Lean_Doc_instHashableMathMode_hash___boxed(
    mut v_x_2173_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_x_28__boxed_2174_: u8 = 0;
    let mut v_res_2175_: u64 = 0;
    let mut v_r_2176_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_x_28__boxed_2174_ = (crate::leanh::lean_unbox(v_x_2173_) as u8);
    v_res_2175_ = l_Lean_Doc_instHashableMathMode_hash(v_x_28__boxed_2174_);
    v_r_2176_ = crate::leanh::lean_box_uint64(v_res_2175_);
    return v_r_2176_;
}
pub unsafe fn l_Lean_Doc_instOrdMathMode_ord(mut v_x_2179_: u8, mut v_y_2180_: u8) -> u8 {
    let mut v___x_2181_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2182_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2183_: u8 = 0;
    v___x_2181_ = l_Lean_Doc_MathMode_ctorIdx(v_x_2179_);
    v___x_2182_ = l_Lean_Doc_MathMode_ctorIdx(v_y_2180_);
    v___x_2183_ = lean_nat_dec_lt(v___x_2181_, v___x_2182_);
    if v___x_2183_ == 0 {
        let mut v___x_2184_: u8 = 0;
        v___x_2184_ = lean_nat_dec_eq(v___x_2181_, v___x_2182_);
        crate::leanh::lean_dec(v___x_2182_);
        crate::leanh::lean_dec(v___x_2181_);
        if v___x_2184_ == 0 {
            let mut v___x_2185_: u8 = 0;
            v___x_2185_ = 2;
            return v___x_2185_;
        } else {
            let mut v___x_2186_: u8 = 0;
            v___x_2186_ = 1;
            return v___x_2186_;
        }
    } else {
        let mut v___x_2187_: u8 = 0;
        crate::leanh::lean_dec(v___x_2182_);
        crate::leanh::lean_dec(v___x_2181_);
        v___x_2187_ = 0;
        return v___x_2187_;
    }
}
pub unsafe fn l_Lean_Doc_instOrdMathMode_ord___boxed(
    mut v_x_2188_: *mut crate::leanh::LeanObject,
    mut v_y_2189_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_x_30__boxed_2190_: u8 = 0;
    let mut v_y_31__boxed_2191_: u8 = 0;
    let mut v_res_2192_: u8 = 0;
    let mut v_r_2193_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_x_30__boxed_2190_ = (crate::leanh::lean_unbox(v_x_2188_) as u8);
    v_y_31__boxed_2191_ = (crate::leanh::lean_unbox(v_y_2189_) as u8);
    v_res_2192_ = l_Lean_Doc_instOrdMathMode_ord(v_x_30__boxed_2190_, v_y_31__boxed_2191_);
    v_r_2193_ = crate::leanh::lean_box((v_res_2192_) as usize);
    return v_r_2193_;
}
pub unsafe fn l_Lean_Doc_Inline_ctorIdx___redArg(
    mut v_x_2196_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    match crate::leanh::lean_obj_tag(v_x_2196_) {
        0 => {
            let mut v___x_2197_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_2197_ = crate::leanh::lean_unsigned_to_nat(0);
            return v___x_2197_;
        }
        1 => {
            let mut v___x_2198_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_2198_ = crate::leanh::lean_unsigned_to_nat(1);
            return v___x_2198_;
        }
        2 => {
            let mut v___x_2199_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_2199_ = crate::leanh::lean_unsigned_to_nat(2);
            return v___x_2199_;
        }
        3 => {
            let mut v___x_2200_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_2200_ = crate::leanh::lean_unsigned_to_nat(3);
            return v___x_2200_;
        }
        4 => {
            let mut v___x_2201_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_2201_ = crate::leanh::lean_unsigned_to_nat(4);
            return v___x_2201_;
        }
        5 => {
            let mut v___x_2202_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_2202_ = crate::leanh::lean_unsigned_to_nat(5);
            return v___x_2202_;
        }
        6 => {
            let mut v___x_2203_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_2203_ = crate::leanh::lean_unsigned_to_nat(6);
            return v___x_2203_;
        }
        7 => {
            let mut v___x_2204_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_2204_ = crate::leanh::lean_unsigned_to_nat(7);
            return v___x_2204_;
        }
        8 => {
            let mut v___x_2205_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_2205_ = crate::leanh::lean_unsigned_to_nat(8);
            return v___x_2205_;
        }
        9 => {
            let mut v___x_2206_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_2206_ = crate::leanh::lean_unsigned_to_nat(9);
            return v___x_2206_;
        }
        _ => {
            let mut v___x_2207_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_2207_ = crate::leanh::lean_unsigned_to_nat(10);
            return v___x_2207_;
        }
    }
}
pub unsafe fn l_Lean_Doc_Inline_ctorIdx___redArg___boxed(
    mut v_x_2208_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2209_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2209_ = l_Lean_Doc_Inline_ctorIdx___redArg(v_x_2208_);
    crate::leanh::lean_dec_ref(v_x_2208_);
    return v_res_2209_;
}
pub unsafe fn l_Lean_Doc_Inline_ctorIdx(
    mut v_i_2210_: *mut crate::leanh::LeanObject,
    mut v_x_2211_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2212_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2212_ = l_Lean_Doc_Inline_ctorIdx___redArg(v_x_2211_);
    return v___x_2212_;
}
pub unsafe fn l_Lean_Doc_Inline_ctorIdx___boxed(
    mut v_i_2213_: *mut crate::leanh::LeanObject,
    mut v_x_2214_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2215_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2215_ = l_Lean_Doc_Inline_ctorIdx(v_i_2213_, v_x_2214_);
    crate::leanh::lean_dec_ref(v_x_2214_);
    return v_res_2215_;
}
pub unsafe fn l_Lean_Doc_Inline_ctorElim___redArg(
    mut v_t_2216_: *mut crate::leanh::LeanObject,
    mut v_k_2217_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    match crate::leanh::lean_obj_tag(v_t_2216_) {
        4 => {
            let mut v_mode_2218_: u8 = 0;
            let mut v_string_2219_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_2220_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_2221_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v_mode_2218_ = crate::leanh::lean_ctor_get_uint8(
                v_t_2216_,
                (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
            );
            v_string_2219_ = crate::leanh::lean_ctor_get(v_t_2216_, 0);
            crate::leanh::lean_inc_ref(v_string_2219_);
            crate::leanh::lean_dec_ref_known(v_t_2216_, 1);
            v___x_2220_ = crate::leanh::lean_box((v_mode_2218_) as usize);
            v___x_2221_ = crate::leanh::lean_apply_2(v_k_2217_, v___x_2220_, v_string_2219_);
            return v___x_2221_;
        }
        6 => {
            let mut v_content_2222_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_url_2223_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_2224_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v_content_2222_ = crate::leanh::lean_ctor_get(v_t_2216_, 0);
            crate::leanh::lean_inc_ref(v_content_2222_);
            v_url_2223_ = crate::leanh::lean_ctor_get(v_t_2216_, 1);
            crate::leanh::lean_inc_ref(v_url_2223_);
            crate::leanh::lean_dec_ref_known(v_t_2216_, 2);
            v___x_2224_ = crate::leanh::lean_apply_2(v_k_2217_, v_content_2222_, v_url_2223_);
            return v___x_2224_;
        }
        7 => {
            let mut v_name_2225_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_content_2226_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_2227_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v_name_2225_ = crate::leanh::lean_ctor_get(v_t_2216_, 0);
            crate::leanh::lean_inc_ref(v_name_2225_);
            v_content_2226_ = crate::leanh::lean_ctor_get(v_t_2216_, 1);
            crate::leanh::lean_inc_ref(v_content_2226_);
            crate::leanh::lean_dec_ref_known(v_t_2216_, 2);
            v___x_2227_ = crate::leanh::lean_apply_2(v_k_2217_, v_name_2225_, v_content_2226_);
            return v___x_2227_;
        }
        8 => {
            let mut v_alt_2228_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_url_2229_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_2230_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v_alt_2228_ = crate::leanh::lean_ctor_get(v_t_2216_, 0);
            crate::leanh::lean_inc_ref(v_alt_2228_);
            v_url_2229_ = crate::leanh::lean_ctor_get(v_t_2216_, 1);
            crate::leanh::lean_inc_ref(v_url_2229_);
            crate::leanh::lean_dec_ref_known(v_t_2216_, 2);
            v___x_2230_ = crate::leanh::lean_apply_2(v_k_2217_, v_alt_2228_, v_url_2229_);
            return v___x_2230_;
        }
        10 => {
            let mut v_container_2231_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_content_2232_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_2233_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v_container_2231_ = crate::leanh::lean_ctor_get(v_t_2216_, 0);
            crate::leanh::lean_inc(v_container_2231_);
            v_content_2232_ = crate::leanh::lean_ctor_get(v_t_2216_, 1);
            crate::leanh::lean_inc_ref(v_content_2232_);
            crate::leanh::lean_dec_ref_known(v_t_2216_, 2);
            v___x_2233_ = crate::leanh::lean_apply_2(v_k_2217_, v_container_2231_, v_content_2232_);
            return v___x_2233_;
        }
        _ => {
            let mut v_string_2234_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_2235_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v_string_2234_ = crate::leanh::lean_ctor_get(v_t_2216_, 0);
            crate::leanh::lean_inc_ref(v_string_2234_);
            crate::leanh::lean_dec_ref(v_t_2216_);
            v___x_2235_ = crate::leanh::lean_apply_1(v_k_2217_, v_string_2234_);
            return v___x_2235_;
        }
    }
}
pub unsafe fn l_Lean_Doc_Inline_ctorElim(
    mut v_i_2236_: *mut crate::leanh::LeanObject,
    mut v_motive__1_2237_: *mut crate::leanh::LeanObject,
    mut v_ctorIdx_2238_: *mut crate::leanh::LeanObject,
    mut v_t_2239_: *mut crate::leanh::LeanObject,
    mut v_h_2240_: *mut crate::leanh::LeanObject,
    mut v_k_2241_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2242_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2242_ = l_Lean_Doc_Inline_ctorElim___redArg(v_t_2239_, v_k_2241_);
    return v___x_2242_;
}
pub unsafe fn l_Lean_Doc_Inline_ctorElim___boxed(
    mut v_i_2243_: *mut crate::leanh::LeanObject,
    mut v_motive__1_2244_: *mut crate::leanh::LeanObject,
    mut v_ctorIdx_2245_: *mut crate::leanh::LeanObject,
    mut v_t_2246_: *mut crate::leanh::LeanObject,
    mut v_h_2247_: *mut crate::leanh::LeanObject,
    mut v_k_2248_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2249_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2249_ = l_Lean_Doc_Inline_ctorElim(
        v_i_2243_,
        v_motive__1_2244_,
        v_ctorIdx_2245_,
        v_t_2246_,
        v_h_2247_,
        v_k_2248_,
    );
    crate::leanh::lean_dec(v_ctorIdx_2245_);
    return v_res_2249_;
}
pub unsafe fn l_Lean_Doc_Inline_text_elim___redArg(
    mut v_t_2250_: *mut crate::leanh::LeanObject,
    mut v_text_2251_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2252_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2252_ = l_Lean_Doc_Inline_ctorElim___redArg(v_t_2250_, v_text_2251_);
    return v___x_2252_;
}
pub unsafe fn l_Lean_Doc_Inline_text_elim(
    mut v_i_2253_: *mut crate::leanh::LeanObject,
    mut v_motive__1_2254_: *mut crate::leanh::LeanObject,
    mut v_t_2255_: *mut crate::leanh::LeanObject,
    mut v_h_2256_: *mut crate::leanh::LeanObject,
    mut v_text_2257_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2258_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2258_ = l_Lean_Doc_Inline_ctorElim___redArg(v_t_2255_, v_text_2257_);
    return v___x_2258_;
}
pub unsafe fn l_Lean_Doc_Inline_emph_elim___redArg(
    mut v_t_2259_: *mut crate::leanh::LeanObject,
    mut v_emph_2260_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2261_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2261_ = l_Lean_Doc_Inline_ctorElim___redArg(v_t_2259_, v_emph_2260_);
    return v___x_2261_;
}
pub unsafe fn l_Lean_Doc_Inline_emph_elim(
    mut v_i_2262_: *mut crate::leanh::LeanObject,
    mut v_motive__1_2263_: *mut crate::leanh::LeanObject,
    mut v_t_2264_: *mut crate::leanh::LeanObject,
    mut v_h_2265_: *mut crate::leanh::LeanObject,
    mut v_emph_2266_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2267_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2267_ = l_Lean_Doc_Inline_ctorElim___redArg(v_t_2264_, v_emph_2266_);
    return v___x_2267_;
}
pub unsafe fn l_Lean_Doc_Inline_bold_elim___redArg(
    mut v_t_2268_: *mut crate::leanh::LeanObject,
    mut v_bold_2269_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2270_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2270_ = l_Lean_Doc_Inline_ctorElim___redArg(v_t_2268_, v_bold_2269_);
    return v___x_2270_;
}
pub unsafe fn l_Lean_Doc_Inline_bold_elim(
    mut v_i_2271_: *mut crate::leanh::LeanObject,
    mut v_motive__1_2272_: *mut crate::leanh::LeanObject,
    mut v_t_2273_: *mut crate::leanh::LeanObject,
    mut v_h_2274_: *mut crate::leanh::LeanObject,
    mut v_bold_2275_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2276_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2276_ = l_Lean_Doc_Inline_ctorElim___redArg(v_t_2273_, v_bold_2275_);
    return v___x_2276_;
}
pub unsafe fn l_Lean_Doc_Inline_code_elim___redArg(
    mut v_t_2277_: *mut crate::leanh::LeanObject,
    mut v_code_2278_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2279_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2279_ = l_Lean_Doc_Inline_ctorElim___redArg(v_t_2277_, v_code_2278_);
    return v___x_2279_;
}
pub unsafe fn l_Lean_Doc_Inline_code_elim(
    mut v_i_2280_: *mut crate::leanh::LeanObject,
    mut v_motive__1_2281_: *mut crate::leanh::LeanObject,
    mut v_t_2282_: *mut crate::leanh::LeanObject,
    mut v_h_2283_: *mut crate::leanh::LeanObject,
    mut v_code_2284_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2285_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2285_ = l_Lean_Doc_Inline_ctorElim___redArg(v_t_2282_, v_code_2284_);
    return v___x_2285_;
}
pub unsafe fn l_Lean_Doc_Inline_math_elim___redArg(
    mut v_t_2286_: *mut crate::leanh::LeanObject,
    mut v_math_2287_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2288_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2288_ = l_Lean_Doc_Inline_ctorElim___redArg(v_t_2286_, v_math_2287_);
    return v___x_2288_;
}
pub unsafe fn l_Lean_Doc_Inline_math_elim(
    mut v_i_2289_: *mut crate::leanh::LeanObject,
    mut v_motive__1_2290_: *mut crate::leanh::LeanObject,
    mut v_t_2291_: *mut crate::leanh::LeanObject,
    mut v_h_2292_: *mut crate::leanh::LeanObject,
    mut v_math_2293_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2294_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2294_ = l_Lean_Doc_Inline_ctorElim___redArg(v_t_2291_, v_math_2293_);
    return v___x_2294_;
}
pub unsafe fn l_Lean_Doc_Inline_linebreak_elim___redArg(
    mut v_t_2295_: *mut crate::leanh::LeanObject,
    mut v_linebreak_2296_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2297_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2297_ = l_Lean_Doc_Inline_ctorElim___redArg(v_t_2295_, v_linebreak_2296_);
    return v___x_2297_;
}
pub unsafe fn l_Lean_Doc_Inline_linebreak_elim(
    mut v_i_2298_: *mut crate::leanh::LeanObject,
    mut v_motive__1_2299_: *mut crate::leanh::LeanObject,
    mut v_t_2300_: *mut crate::leanh::LeanObject,
    mut v_h_2301_: *mut crate::leanh::LeanObject,
    mut v_linebreak_2302_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2303_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2303_ = l_Lean_Doc_Inline_ctorElim___redArg(v_t_2300_, v_linebreak_2302_);
    return v___x_2303_;
}
pub unsafe fn l_Lean_Doc_Inline_link_elim___redArg(
    mut v_t_2304_: *mut crate::leanh::LeanObject,
    mut v_link_2305_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2306_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2306_ = l_Lean_Doc_Inline_ctorElim___redArg(v_t_2304_, v_link_2305_);
    return v___x_2306_;
}
pub unsafe fn l_Lean_Doc_Inline_link_elim(
    mut v_i_2307_: *mut crate::leanh::LeanObject,
    mut v_motive__1_2308_: *mut crate::leanh::LeanObject,
    mut v_t_2309_: *mut crate::leanh::LeanObject,
    mut v_h_2310_: *mut crate::leanh::LeanObject,
    mut v_link_2311_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2312_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2312_ = l_Lean_Doc_Inline_ctorElim___redArg(v_t_2309_, v_link_2311_);
    return v___x_2312_;
}
pub unsafe fn l_Lean_Doc_Inline_footnote_elim___redArg(
    mut v_t_2313_: *mut crate::leanh::LeanObject,
    mut v_footnote_2314_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2315_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2315_ = l_Lean_Doc_Inline_ctorElim___redArg(v_t_2313_, v_footnote_2314_);
    return v___x_2315_;
}
pub unsafe fn l_Lean_Doc_Inline_footnote_elim(
    mut v_i_2316_: *mut crate::leanh::LeanObject,
    mut v_motive__1_2317_: *mut crate::leanh::LeanObject,
    mut v_t_2318_: *mut crate::leanh::LeanObject,
    mut v_h_2319_: *mut crate::leanh::LeanObject,
    mut v_footnote_2320_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2321_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2321_ = l_Lean_Doc_Inline_ctorElim___redArg(v_t_2318_, v_footnote_2320_);
    return v___x_2321_;
}
pub unsafe fn l_Lean_Doc_Inline_image_elim___redArg(
    mut v_t_2322_: *mut crate::leanh::LeanObject,
    mut v_image_2323_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2324_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2324_ = l_Lean_Doc_Inline_ctorElim___redArg(v_t_2322_, v_image_2323_);
    return v___x_2324_;
}
pub unsafe fn l_Lean_Doc_Inline_image_elim(
    mut v_i_2325_: *mut crate::leanh::LeanObject,
    mut v_motive__1_2326_: *mut crate::leanh::LeanObject,
    mut v_t_2327_: *mut crate::leanh::LeanObject,
    mut v_h_2328_: *mut crate::leanh::LeanObject,
    mut v_image_2329_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2330_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2330_ = l_Lean_Doc_Inline_ctorElim___redArg(v_t_2327_, v_image_2329_);
    return v___x_2330_;
}
pub unsafe fn l_Lean_Doc_Inline_concat_elim___redArg(
    mut v_t_2331_: *mut crate::leanh::LeanObject,
    mut v_concat_2332_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2333_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2333_ = l_Lean_Doc_Inline_ctorElim___redArg(v_t_2331_, v_concat_2332_);
    return v___x_2333_;
}
pub unsafe fn l_Lean_Doc_Inline_concat_elim(
    mut v_i_2334_: *mut crate::leanh::LeanObject,
    mut v_motive__1_2335_: *mut crate::leanh::LeanObject,
    mut v_t_2336_: *mut crate::leanh::LeanObject,
    mut v_h_2337_: *mut crate::leanh::LeanObject,
    mut v_concat_2338_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2339_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2339_ = l_Lean_Doc_Inline_ctorElim___redArg(v_t_2336_, v_concat_2338_);
    return v___x_2339_;
}
pub unsafe fn l_Lean_Doc_Inline_other_elim___redArg(
    mut v_t_2340_: *mut crate::leanh::LeanObject,
    mut v_other_2341_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2342_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2342_ = l_Lean_Doc_Inline_ctorElim___redArg(v_t_2340_, v_other_2341_);
    return v___x_2342_;
}
pub unsafe fn l_Lean_Doc_Inline_other_elim(
    mut v_i_2343_: *mut crate::leanh::LeanObject,
    mut v_motive__1_2344_: *mut crate::leanh::LeanObject,
    mut v_t_2345_: *mut crate::leanh::LeanObject,
    mut v_h_2346_: *mut crate::leanh::LeanObject,
    mut v_other_2347_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2348_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2348_ = l_Lean_Doc_Inline_ctorElim___redArg(v_t_2345_, v_other_2347_);
    return v___x_2348_;
}
pub unsafe fn l_Lean_Doc_instBEqInline_beq___redArg___boxed(
    mut v_inst_2349_: *mut crate::leanh::LeanObject,
    mut v_x_2350_: *mut crate::leanh::LeanObject,
    mut v_x_2351_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2352_: u8 = 0;
    let mut v_r_2353_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2352_ = l_Lean_Doc_instBEqInline_beq___redArg(v_inst_2349_, v_x_2350_, v_x_2351_);
    v_r_2353_ = crate::leanh::lean_box((v_res_2352_) as usize);
    return v_r_2353_;
}
pub unsafe fn l_Lean_Doc_instBEqInline_beq___redArg(
    mut v_inst_2354_: *mut crate::leanh::LeanObject,
    mut v_x_2355_: *mut crate::leanh::LeanObject,
    mut v_x_2356_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_2357_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2358_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2359_: u8 = 0;
    let mut v___x_2360_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_content_2362_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_content_x27_2363_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2364_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2365_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2366_: u8 = 0;
    let mut v___x_2367_: u8 = 0;
    let mut v_content_2368_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_content_2369_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_content_2370_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_content_2371_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_mode_2372_: u8 = 0;
    let mut v_string_2373_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_mode_2374_: u8 = 0;
    let mut v_string_2375_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2376_: u8 = 0;
    let mut v___x_2377_: u8 = 0;
    let mut v_content_2378_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_url_2379_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_content_2380_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_url_2381_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2382_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2383_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2384_: u8 = 0;
    let mut v___x_2385_: u8 = 0;
    let mut v___x_2386_: u8 = 0;
    let mut v_name_2387_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_content_2388_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_name_2389_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_content_2390_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2391_: u8 = 0;
    let mut v___x_2392_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2393_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2394_: u8 = 0;
    let mut v___x_2395_: u8 = 0;
    let mut v_alt_2396_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_url_2397_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_alt_2398_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_url_2399_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2400_: u8 = 0;
    let mut v___x_2401_: u8 = 0;
    let mut v_content_2402_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_content_2403_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_container_2404_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_content_2405_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_container_2406_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_content_2407_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2408_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2409_: u8 = 0;
    let mut v___x_2410_: u8 = 0;
    let mut v___x_2411_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2412_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2413_: u8 = 0;
    let mut v___x_2414_: u8 = 0;
    let mut v_string_2415_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_string_2416_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2417_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2357_ = l_Lean_Doc_Inline_ctorIdx___redArg(v_x_2355_);
                v___x_2358_ = l_Lean_Doc_Inline_ctorIdx___redArg(v_x_2356_);
                v___x_2359_ = lean_nat_dec_eq(v___x_2357_, v___x_2358_);
                crate::leanh::lean_dec(v___x_2358_);
                crate::leanh::lean_dec(v___x_2357_);
                if v___x_2359_ == 0 {
                    crate::leanh::lean_dec_ref(v_x_2356_);
                    crate::leanh::lean_dec_ref(v_x_2355_);
                    crate::leanh::lean_dec_ref(v_inst_2354_);
                    return v___x_2359_;
                } else {
                    crate::leanh::lean_inc_ref(v_inst_2354_);
                    v___x_2360_ = crate::leanh::lean_alloc_closure(
                        l_Lean_Doc_instBEqInline_beq___redArg___boxed as *mut core::ffi::c_void,
                        3,
                        1,
                    );
                    crate::leanh::lean_closure_set(v___x_2360_, 0, v_inst_2354_);
                    match crate::leanh::lean_obj_tag(v_x_2355_) {
                        1 => {
                            crate::leanh::lean_dec_ref(v_inst_2354_);
                            v_content_2368_ = crate::leanh::lean_ctor_get(v_x_2355_, 0);
                            crate::leanh::lean_inc_ref(v_content_2368_);
                            crate::leanh::lean_dec_ref_known(v_x_2355_, 1);
                            v_content_2369_ = crate::leanh::lean_ctor_get(v_x_2356_, 0);
                            crate::leanh::lean_inc_ref(v_content_2369_);
                            crate::leanh::lean_dec_ref(v_x_2356_);
                            v_content_2362_ = v_content_2368_;
                            v_content_x27_2363_ = v_content_2369_;
                            state = 1;
                            continue;
                        }
                        2 => {
                            crate::leanh::lean_dec_ref(v_inst_2354_);
                            v_content_2370_ = crate::leanh::lean_ctor_get(v_x_2355_, 0);
                            crate::leanh::lean_inc_ref(v_content_2370_);
                            crate::leanh::lean_dec_ref_known(v_x_2355_, 1);
                            v_content_2371_ = crate::leanh::lean_ctor_get(v_x_2356_, 0);
                            crate::leanh::lean_inc_ref(v_content_2371_);
                            crate::leanh::lean_dec_ref(v_x_2356_);
                            v_content_2362_ = v_content_2370_;
                            v_content_x27_2363_ = v_content_2371_;
                            state = 1;
                            continue;
                        }
                        4 => {
                            crate::leanh::lean_dec_ref(v___x_2360_);
                            crate::leanh::lean_dec_ref(v_inst_2354_);
                            v_mode_2372_ = crate::leanh::lean_ctor_get_uint8(
                                v_x_2355_,
                                (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                            );
                            v_string_2373_ = crate::leanh::lean_ctor_get(v_x_2355_, 0);
                            crate::leanh::lean_inc_ref(v_string_2373_);
                            crate::leanh::lean_dec_ref_known(v_x_2355_, 1);
                            v_mode_2374_ = crate::leanh::lean_ctor_get_uint8(
                                v_x_2356_,
                                (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                            );
                            v_string_2375_ = crate::leanh::lean_ctor_get(v_x_2356_, 0);
                            crate::leanh::lean_inc_ref(v_string_2375_);
                            crate::leanh::lean_dec_ref(v_x_2356_);
                            v___x_2376_ =
                                l_Lean_Doc_instBEqMathMode_beq(v_mode_2372_, v_mode_2374_);
                            if v___x_2376_ == 0 {
                                crate::leanh::lean_dec_ref(v_string_2375_);
                                crate::leanh::lean_dec_ref(v_string_2373_);
                                return v___x_2376_;
                            } else {
                                v___x_2377_ = lean_string_dec_eq(v_string_2373_, v_string_2375_);
                                crate::leanh::lean_dec_ref(v_string_2375_);
                                crate::leanh::lean_dec_ref(v_string_2373_);
                                return v___x_2377_;
                            }
                        }
                        6 => {
                            crate::leanh::lean_dec_ref(v_inst_2354_);
                            v_content_2378_ = crate::leanh::lean_ctor_get(v_x_2355_, 0);
                            crate::leanh::lean_inc_ref(v_content_2378_);
                            v_url_2379_ = crate::leanh::lean_ctor_get(v_x_2355_, 1);
                            crate::leanh::lean_inc_ref(v_url_2379_);
                            crate::leanh::lean_dec_ref_known(v_x_2355_, 2);
                            v_content_2380_ = crate::leanh::lean_ctor_get(v_x_2356_, 0);
                            crate::leanh::lean_inc_ref(v_content_2380_);
                            v_url_2381_ = crate::leanh::lean_ctor_get(v_x_2356_, 1);
                            crate::leanh::lean_inc_ref(v_url_2381_);
                            crate::leanh::lean_dec_ref(v_x_2356_);
                            v___x_2382_ = lean_array_get_size(v_content_2378_);
                            v___x_2383_ = lean_array_get_size(v_content_2380_);
                            v___x_2384_ = lean_nat_dec_eq(v___x_2382_, v___x_2383_);
                            if v___x_2384_ == 0 {
                                crate::leanh::lean_dec_ref(v_url_2381_);
                                crate::leanh::lean_dec_ref(v_content_2380_);
                                crate::leanh::lean_dec_ref(v_url_2379_);
                                crate::leanh::lean_dec_ref(v_content_2378_);
                                crate::leanh::lean_dec_ref(v___x_2360_);
                                return v___x_2384_;
                            } else {
                                v___x_2385_ = l_Array_isEqvAux___redArg(
                                    v_content_2378_,
                                    v_content_2380_,
                                    v___x_2360_,
                                    v___x_2382_,
                                );
                                crate::leanh::lean_dec_ref(v_content_2380_);
                                crate::leanh::lean_dec_ref(v_content_2378_);
                                if v___x_2385_ == 0 {
                                    crate::leanh::lean_dec_ref(v_url_2381_);
                                    crate::leanh::lean_dec_ref(v_url_2379_);
                                    return v___x_2385_;
                                } else {
                                    v___x_2386_ = lean_string_dec_eq(v_url_2379_, v_url_2381_);
                                    crate::leanh::lean_dec_ref(v_url_2381_);
                                    crate::leanh::lean_dec_ref(v_url_2379_);
                                    return v___x_2386_;
                                }
                            }
                        }
                        7 => {
                            crate::leanh::lean_dec_ref(v_inst_2354_);
                            v_name_2387_ = crate::leanh::lean_ctor_get(v_x_2355_, 0);
                            crate::leanh::lean_inc_ref(v_name_2387_);
                            v_content_2388_ = crate::leanh::lean_ctor_get(v_x_2355_, 1);
                            crate::leanh::lean_inc_ref(v_content_2388_);
                            crate::leanh::lean_dec_ref_known(v_x_2355_, 2);
                            v_name_2389_ = crate::leanh::lean_ctor_get(v_x_2356_, 0);
                            crate::leanh::lean_inc_ref(v_name_2389_);
                            v_content_2390_ = crate::leanh::lean_ctor_get(v_x_2356_, 1);
                            crate::leanh::lean_inc_ref(v_content_2390_);
                            crate::leanh::lean_dec_ref(v_x_2356_);
                            v___x_2391_ = lean_string_dec_eq(v_name_2387_, v_name_2389_);
                            crate::leanh::lean_dec_ref(v_name_2389_);
                            crate::leanh::lean_dec_ref(v_name_2387_);
                            if v___x_2391_ == 0 {
                                crate::leanh::lean_dec_ref(v_content_2390_);
                                crate::leanh::lean_dec_ref(v_content_2388_);
                                crate::leanh::lean_dec_ref(v___x_2360_);
                                return v___x_2391_;
                            } else {
                                v___x_2392_ = lean_array_get_size(v_content_2388_);
                                v___x_2393_ = lean_array_get_size(v_content_2390_);
                                v___x_2394_ = lean_nat_dec_eq(v___x_2392_, v___x_2393_);
                                if v___x_2394_ == 0 {
                                    crate::leanh::lean_dec_ref(v_content_2390_);
                                    crate::leanh::lean_dec_ref(v_content_2388_);
                                    crate::leanh::lean_dec_ref(v___x_2360_);
                                    return v___x_2394_;
                                } else {
                                    v___x_2395_ = l_Array_isEqvAux___redArg(
                                        v_content_2388_,
                                        v_content_2390_,
                                        v___x_2360_,
                                        v___x_2392_,
                                    );
                                    crate::leanh::lean_dec_ref(v_content_2390_);
                                    crate::leanh::lean_dec_ref(v_content_2388_);
                                    return v___x_2395_;
                                }
                            }
                        }
                        8 => {
                            crate::leanh::lean_dec_ref(v___x_2360_);
                            crate::leanh::lean_dec_ref(v_inst_2354_);
                            v_alt_2396_ = crate::leanh::lean_ctor_get(v_x_2355_, 0);
                            crate::leanh::lean_inc_ref(v_alt_2396_);
                            v_url_2397_ = crate::leanh::lean_ctor_get(v_x_2355_, 1);
                            crate::leanh::lean_inc_ref(v_url_2397_);
                            crate::leanh::lean_dec_ref_known(v_x_2355_, 2);
                            v_alt_2398_ = crate::leanh::lean_ctor_get(v_x_2356_, 0);
                            crate::leanh::lean_inc_ref(v_alt_2398_);
                            v_url_2399_ = crate::leanh::lean_ctor_get(v_x_2356_, 1);
                            crate::leanh::lean_inc_ref(v_url_2399_);
                            crate::leanh::lean_dec_ref(v_x_2356_);
                            v___x_2400_ = lean_string_dec_eq(v_alt_2396_, v_alt_2398_);
                            crate::leanh::lean_dec_ref(v_alt_2398_);
                            crate::leanh::lean_dec_ref(v_alt_2396_);
                            if v___x_2400_ == 0 {
                                crate::leanh::lean_dec_ref(v_url_2399_);
                                crate::leanh::lean_dec_ref(v_url_2397_);
                                return v___x_2400_;
                            } else {
                                v___x_2401_ = lean_string_dec_eq(v_url_2397_, v_url_2399_);
                                crate::leanh::lean_dec_ref(v_url_2399_);
                                crate::leanh::lean_dec_ref(v_url_2397_);
                                return v___x_2401_;
                            }
                        }
                        9 => {
                            crate::leanh::lean_dec_ref(v_inst_2354_);
                            v_content_2402_ = crate::leanh::lean_ctor_get(v_x_2355_, 0);
                            crate::leanh::lean_inc_ref(v_content_2402_);
                            crate::leanh::lean_dec_ref_known(v_x_2355_, 1);
                            v_content_2403_ = crate::leanh::lean_ctor_get(v_x_2356_, 0);
                            crate::leanh::lean_inc_ref(v_content_2403_);
                            crate::leanh::lean_dec_ref(v_x_2356_);
                            v_content_2362_ = v_content_2402_;
                            v_content_x27_2363_ = v_content_2403_;
                            state = 1;
                            continue;
                        }
                        10 => {
                            v_container_2404_ = crate::leanh::lean_ctor_get(v_x_2355_, 0);
                            crate::leanh::lean_inc(v_container_2404_);
                            v_content_2405_ = crate::leanh::lean_ctor_get(v_x_2355_, 1);
                            crate::leanh::lean_inc_ref(v_content_2405_);
                            crate::leanh::lean_dec_ref_known(v_x_2355_, 2);
                            v_container_2406_ = crate::leanh::lean_ctor_get(v_x_2356_, 0);
                            crate::leanh::lean_inc(v_container_2406_);
                            v_content_2407_ = crate::leanh::lean_ctor_get(v_x_2356_, 1);
                            crate::leanh::lean_inc_ref(v_content_2407_);
                            crate::leanh::lean_dec_ref(v_x_2356_);
                            v___x_2408_ = crate::leanh::lean_apply_2(
                                v_inst_2354_,
                                v_container_2404_,
                                v_container_2406_,
                            );
                            v___x_2409_ = (crate::leanh::lean_unbox(v___x_2408_) as u8);
                            if v___x_2409_ == 0 {
                                crate::leanh::lean_dec_ref(v_content_2407_);
                                crate::leanh::lean_dec_ref(v_content_2405_);
                                crate::leanh::lean_dec_ref(v___x_2360_);
                                v___x_2410_ = (crate::leanh::lean_unbox(v___x_2408_) as u8);
                                return v___x_2410_;
                            } else {
                                v___x_2411_ = lean_array_get_size(v_content_2405_);
                                v___x_2412_ = lean_array_get_size(v_content_2407_);
                                v___x_2413_ = lean_nat_dec_eq(v___x_2411_, v___x_2412_);
                                if v___x_2413_ == 0 {
                                    crate::leanh::lean_dec_ref(v_content_2407_);
                                    crate::leanh::lean_dec_ref(v_content_2405_);
                                    crate::leanh::lean_dec_ref(v___x_2360_);
                                    return v___x_2413_;
                                } else {
                                    v___x_2414_ = l_Array_isEqvAux___redArg(
                                        v_content_2405_,
                                        v_content_2407_,
                                        v___x_2360_,
                                        v___x_2411_,
                                    );
                                    crate::leanh::lean_dec_ref(v_content_2407_);
                                    crate::leanh::lean_dec_ref(v_content_2405_);
                                    return v___x_2414_;
                                }
                            }
                        }
                        _ => {
                            crate::leanh::lean_dec_ref(v___x_2360_);
                            crate::leanh::lean_dec_ref(v_inst_2354_);
                            v_string_2415_ = crate::leanh::lean_ctor_get(v_x_2355_, 0);
                            crate::leanh::lean_inc_ref(v_string_2415_);
                            crate::leanh::lean_dec_ref(v_x_2355_);
                            v_string_2416_ = crate::leanh::lean_ctor_get(v_x_2356_, 0);
                            crate::leanh::lean_inc_ref(v_string_2416_);
                            crate::leanh::lean_dec_ref(v_x_2356_);
                            v___x_2417_ = lean_string_dec_eq(v_string_2415_, v_string_2416_);
                            crate::leanh::lean_dec_ref(v_string_2416_);
                            crate::leanh::lean_dec_ref(v_string_2415_);
                            return v___x_2417_;
                        }
                    }
                }
            }
            1 => {
                v___x_2364_ = lean_array_get_size(v_content_2362_);
                v___x_2365_ = lean_array_get_size(v_content_x27_2363_);
                v___x_2366_ = lean_nat_dec_eq(v___x_2364_, v___x_2365_);
                if v___x_2366_ == 0 {
                    crate::leanh::lean_dec_ref(v_content_x27_2363_);
                    crate::leanh::lean_dec_ref(v_content_2362_);
                    crate::leanh::lean_dec_ref(v___x_2360_);
                    return v___x_2366_;
                } else {
                    v___x_2367_ = l_Array_isEqvAux___redArg(
                        v_content_2362_,
                        v_content_x27_2363_,
                        v___x_2360_,
                        v___x_2364_,
                    );
                    crate::leanh::lean_dec_ref(v_content_x27_2363_);
                    crate::leanh::lean_dec_ref(v_content_2362_);
                    return v___x_2367_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Doc_instBEqInline_beq(
    mut v_i_2418_: *mut crate::leanh::LeanObject,
    mut v_inst_2419_: *mut crate::leanh::LeanObject,
    mut v_x_2420_: *mut crate::leanh::LeanObject,
    mut v_x_2421_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_2422_: u8 = 0;
    v___x_2422_ = l_Lean_Doc_instBEqInline_beq___redArg(v_inst_2419_, v_x_2420_, v_x_2421_);
    return v___x_2422_;
}
pub unsafe fn l_Lean_Doc_instBEqInline_beq___boxed(
    mut v_i_2423_: *mut crate::leanh::LeanObject,
    mut v_inst_2424_: *mut crate::leanh::LeanObject,
    mut v_x_2425_: *mut crate::leanh::LeanObject,
    mut v_x_2426_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2427_: u8 = 0;
    let mut v_r_2428_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2427_ = l_Lean_Doc_instBEqInline_beq(v_i_2423_, v_inst_2424_, v_x_2425_, v_x_2426_);
    v_r_2428_ = crate::leanh::lean_box((v_res_2427_) as usize);
    return v_r_2428_;
}
pub unsafe fn l_Lean_Doc_instBEqInline___redArg(
    mut v_inst_2429_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2430_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2430_ = crate::leanh::lean_alloc_closure(
        l_Lean_Doc_instBEqInline_beq___boxed as *mut core::ffi::c_void,
        4,
        2,
    );
    crate::leanh::lean_closure_set(v___x_2430_, 0, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_2430_, 1, v_inst_2429_);
    return v___x_2430_;
}
pub unsafe fn l_Lean_Doc_instBEqInline(
    mut v_i_2431_: *mut crate::leanh::LeanObject,
    mut v_inst_2432_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2433_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2433_ = crate::leanh::lean_alloc_closure(
        l_Lean_Doc_instBEqInline_beq___boxed as *mut core::ffi::c_void,
        4,
        2,
    );
    crate::leanh::lean_closure_set(v___x_2433_, 0, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_2433_, 1, v_inst_2432_);
    return v___x_2433_;
}
pub unsafe fn l_Lean_Doc_instOrdInline_ord___redArg___boxed(
    mut v_inst_2434_: *mut crate::leanh::LeanObject,
    mut v_x_2435_: *mut crate::leanh::LeanObject,
    mut v_x_2436_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2437_: u8 = 0;
    let mut v_r_2438_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2437_ = l_Lean_Doc_instOrdInline_ord___redArg(v_inst_2434_, v_x_2435_, v_x_2436_);
    v_r_2438_ = crate::leanh::lean_box((v_res_2437_) as usize);
    return v_r_2438_;
}
pub unsafe fn l_Lean_Doc_instOrdInline_ord___redArg(
    mut v_inst_2439_: *mut crate::leanh::LeanObject,
    mut v_x_2440_: *mut crate::leanh::LeanObject,
    mut v_x_2441_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v_string_2443_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_string_x27_2444_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2445_: u8 = 0;
    let mut v___x_2446_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2447_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2448_: u8 = 0;
    let mut v___x_2449_: u8 = 0;
    let mut v___x_2450_: u8 = 0;
    let mut v___x_2451_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_content_2453_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_content_x27_2454_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2455_: u8 = 0;
    let mut v_content_2456_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_content_2457_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_content_2458_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_content_2459_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_mode_2460_: u8 = 0;
    let mut v_string_2461_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_mode_2462_: u8 = 0;
    let mut v_string_2463_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2464_: u8 = 0;
    let mut v___x_2465_: u8 = 0;
    let mut v_content_2466_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_url_2467_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_content_2468_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_url_2469_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2470_: u8 = 0;
    let mut v___x_2471_: u8 = 0;
    let mut v_name_2472_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_content_2473_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_name_2474_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_content_2475_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2476_: u8 = 0;
    let mut v___x_2477_: u8 = 0;
    let mut v_alt_2478_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_url_2479_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_alt_2480_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_url_2481_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2482_: u8 = 0;
    let mut v___x_2483_: u8 = 0;
    let mut v_content_2484_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_content_2485_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_container_2486_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_content_2487_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_container_2488_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_content_2489_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2490_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2491_: u8 = 0;
    let mut v___x_2492_: u8 = 0;
    let mut v___x_2493_: u8 = 0;
    let mut v_string_2494_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_string_2495_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2496_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2446_ = l_Lean_Doc_Inline_ctorIdx___redArg(v_x_2440_);
                v___x_2447_ = l_Lean_Doc_Inline_ctorIdx___redArg(v_x_2441_);
                v___x_2448_ = lean_nat_dec_lt(v___x_2446_, v___x_2447_);
                if v___x_2448_ == 0 {
                    v___x_2449_ = lean_nat_dec_eq(v___x_2446_, v___x_2447_);
                    crate::leanh::lean_dec(v___x_2447_);
                    crate::leanh::lean_dec(v___x_2446_);
                    if v___x_2449_ == 0 {
                        crate::leanh::lean_dec_ref(v_x_2441_);
                        crate::leanh::lean_dec_ref(v_x_2440_);
                        crate::leanh::lean_dec_ref(v_inst_2439_);
                        v___x_2450_ = 2;
                        return v___x_2450_;
                    } else {
                        crate::leanh::lean_inc_ref(v_inst_2439_);
                        v___x_2451_ = crate::leanh::lean_alloc_closure(
                            l_Lean_Doc_instOrdInline_ord___redArg___boxed as *mut core::ffi::c_void,
                            3,
                            1,
                        );
                        crate::leanh::lean_closure_set(v___x_2451_, 0, v_inst_2439_);
                        match crate::leanh::lean_obj_tag(v_x_2440_) {
                            1 => {
                                crate::leanh::lean_dec_ref(v_inst_2439_);
                                v_content_2456_ = crate::leanh::lean_ctor_get(v_x_2440_, 0);
                                crate::leanh::lean_inc_ref(v_content_2456_);
                                crate::leanh::lean_dec_ref_known(v_x_2440_, 1);
                                v_content_2457_ = crate::leanh::lean_ctor_get(v_x_2441_, 0);
                                crate::leanh::lean_inc_ref(v_content_2457_);
                                crate::leanh::lean_dec_ref(v_x_2441_);
                                v_content_2453_ = v_content_2456_;
                                v_content_x27_2454_ = v_content_2457_;
                                state = 2;
                                continue;
                            }
                            2 => {
                                crate::leanh::lean_dec_ref(v_inst_2439_);
                                v_content_2458_ = crate::leanh::lean_ctor_get(v_x_2440_, 0);
                                crate::leanh::lean_inc_ref(v_content_2458_);
                                crate::leanh::lean_dec_ref_known(v_x_2440_, 1);
                                v_content_2459_ = crate::leanh::lean_ctor_get(v_x_2441_, 0);
                                crate::leanh::lean_inc_ref(v_content_2459_);
                                crate::leanh::lean_dec_ref(v_x_2441_);
                                v_content_2453_ = v_content_2458_;
                                v_content_x27_2454_ = v_content_2459_;
                                state = 2;
                                continue;
                            }
                            4 => {
                                crate::leanh::lean_dec_ref(v___x_2451_);
                                crate::leanh::lean_dec_ref(v_inst_2439_);
                                v_mode_2460_ = crate::leanh::lean_ctor_get_uint8(
                                    v_x_2440_,
                                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1)
                                        as u32,
                                );
                                v_string_2461_ = crate::leanh::lean_ctor_get(v_x_2440_, 0);
                                crate::leanh::lean_inc_ref(v_string_2461_);
                                crate::leanh::lean_dec_ref_known(v_x_2440_, 1);
                                v_mode_2462_ = crate::leanh::lean_ctor_get_uint8(
                                    v_x_2441_,
                                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1)
                                        as u32,
                                );
                                v_string_2463_ = crate::leanh::lean_ctor_get(v_x_2441_, 0);
                                crate::leanh::lean_inc_ref(v_string_2463_);
                                crate::leanh::lean_dec_ref(v_x_2441_);
                                v___x_2464_ =
                                    l_Lean_Doc_instOrdMathMode_ord(v_mode_2460_, v_mode_2462_);
                                if v___x_2464_ == 1 {
                                    v___x_2465_ =
                                        lean_string_compare(v_string_2461_, v_string_2463_);
                                    crate::leanh::lean_dec_ref(v_string_2463_);
                                    crate::leanh::lean_dec_ref(v_string_2461_);
                                    if v___x_2465_ == 1 {
                                        return v___x_2465_;
                                    } else {
                                        return v___x_2465_;
                                    }
                                } else {
                                    crate::leanh::lean_dec_ref(v_string_2463_);
                                    crate::leanh::lean_dec_ref(v_string_2461_);
                                    return v___x_2464_;
                                }
                            }
                            6 => {
                                crate::leanh::lean_dec_ref(v_inst_2439_);
                                v_content_2466_ = crate::leanh::lean_ctor_get(v_x_2440_, 0);
                                crate::leanh::lean_inc_ref(v_content_2466_);
                                v_url_2467_ = crate::leanh::lean_ctor_get(v_x_2440_, 1);
                                crate::leanh::lean_inc_ref(v_url_2467_);
                                crate::leanh::lean_dec_ref_known(v_x_2440_, 2);
                                v_content_2468_ = crate::leanh::lean_ctor_get(v_x_2441_, 0);
                                crate::leanh::lean_inc_ref(v_content_2468_);
                                v_url_2469_ = crate::leanh::lean_ctor_get(v_x_2441_, 1);
                                crate::leanh::lean_inc_ref(v_url_2469_);
                                crate::leanh::lean_dec_ref(v_x_2441_);
                                v___x_2470_ = l_Array_compareLex___redArg(
                                    v___x_2451_,
                                    v_content_2466_,
                                    v_content_2468_,
                                );
                                crate::leanh::lean_dec_ref(v_content_2468_);
                                crate::leanh::lean_dec_ref(v_content_2466_);
                                if v___x_2470_ == 1 {
                                    v___x_2471_ = lean_string_compare(v_url_2467_, v_url_2469_);
                                    crate::leanh::lean_dec_ref(v_url_2469_);
                                    crate::leanh::lean_dec_ref(v_url_2467_);
                                    if v___x_2471_ == 1 {
                                        return v___x_2471_;
                                    } else {
                                        return v___x_2471_;
                                    }
                                } else {
                                    crate::leanh::lean_dec_ref(v_url_2469_);
                                    crate::leanh::lean_dec_ref(v_url_2467_);
                                    return v___x_2470_;
                                }
                            }
                            7 => {
                                crate::leanh::lean_dec_ref(v_inst_2439_);
                                v_name_2472_ = crate::leanh::lean_ctor_get(v_x_2440_, 0);
                                crate::leanh::lean_inc_ref(v_name_2472_);
                                v_content_2473_ = crate::leanh::lean_ctor_get(v_x_2440_, 1);
                                crate::leanh::lean_inc_ref(v_content_2473_);
                                crate::leanh::lean_dec_ref_known(v_x_2440_, 2);
                                v_name_2474_ = crate::leanh::lean_ctor_get(v_x_2441_, 0);
                                crate::leanh::lean_inc_ref(v_name_2474_);
                                v_content_2475_ = crate::leanh::lean_ctor_get(v_x_2441_, 1);
                                crate::leanh::lean_inc_ref(v_content_2475_);
                                crate::leanh::lean_dec_ref(v_x_2441_);
                                v___x_2476_ = lean_string_compare(v_name_2472_, v_name_2474_);
                                crate::leanh::lean_dec_ref(v_name_2474_);
                                crate::leanh::lean_dec_ref(v_name_2472_);
                                if v___x_2476_ == 1 {
                                    v___x_2477_ = l_Array_compareLex___redArg(
                                        v___x_2451_,
                                        v_content_2473_,
                                        v_content_2475_,
                                    );
                                    crate::leanh::lean_dec_ref(v_content_2475_);
                                    crate::leanh::lean_dec_ref(v_content_2473_);
                                    if v___x_2477_ == 1 {
                                        return v___x_2477_;
                                    } else {
                                        return v___x_2477_;
                                    }
                                } else {
                                    crate::leanh::lean_dec_ref(v_content_2475_);
                                    crate::leanh::lean_dec_ref(v_content_2473_);
                                    crate::leanh::lean_dec_ref(v___x_2451_);
                                    return v___x_2476_;
                                }
                            }
                            8 => {
                                crate::leanh::lean_dec_ref(v___x_2451_);
                                crate::leanh::lean_dec_ref(v_inst_2439_);
                                v_alt_2478_ = crate::leanh::lean_ctor_get(v_x_2440_, 0);
                                crate::leanh::lean_inc_ref(v_alt_2478_);
                                v_url_2479_ = crate::leanh::lean_ctor_get(v_x_2440_, 1);
                                crate::leanh::lean_inc_ref(v_url_2479_);
                                crate::leanh::lean_dec_ref_known(v_x_2440_, 2);
                                v_alt_2480_ = crate::leanh::lean_ctor_get(v_x_2441_, 0);
                                crate::leanh::lean_inc_ref(v_alt_2480_);
                                v_url_2481_ = crate::leanh::lean_ctor_get(v_x_2441_, 1);
                                crate::leanh::lean_inc_ref(v_url_2481_);
                                crate::leanh::lean_dec_ref(v_x_2441_);
                                v___x_2482_ = lean_string_compare(v_alt_2478_, v_alt_2480_);
                                crate::leanh::lean_dec_ref(v_alt_2480_);
                                crate::leanh::lean_dec_ref(v_alt_2478_);
                                if v___x_2482_ == 1 {
                                    v___x_2483_ = lean_string_compare(v_url_2479_, v_url_2481_);
                                    crate::leanh::lean_dec_ref(v_url_2481_);
                                    crate::leanh::lean_dec_ref(v_url_2479_);
                                    if v___x_2483_ == 1 {
                                        return v___x_2483_;
                                    } else {
                                        return v___x_2483_;
                                    }
                                } else {
                                    crate::leanh::lean_dec_ref(v_url_2481_);
                                    crate::leanh::lean_dec_ref(v_url_2479_);
                                    return v___x_2482_;
                                }
                            }
                            9 => {
                                crate::leanh::lean_dec_ref(v_inst_2439_);
                                v_content_2484_ = crate::leanh::lean_ctor_get(v_x_2440_, 0);
                                crate::leanh::lean_inc_ref(v_content_2484_);
                                crate::leanh::lean_dec_ref_known(v_x_2440_, 1);
                                v_content_2485_ = crate::leanh::lean_ctor_get(v_x_2441_, 0);
                                crate::leanh::lean_inc_ref(v_content_2485_);
                                crate::leanh::lean_dec_ref(v_x_2441_);
                                v_content_2453_ = v_content_2484_;
                                v_content_x27_2454_ = v_content_2485_;
                                state = 2;
                                continue;
                            }
                            10 => {
                                v_container_2486_ = crate::leanh::lean_ctor_get(v_x_2440_, 0);
                                crate::leanh::lean_inc(v_container_2486_);
                                v_content_2487_ = crate::leanh::lean_ctor_get(v_x_2440_, 1);
                                crate::leanh::lean_inc_ref(v_content_2487_);
                                crate::leanh::lean_dec_ref_known(v_x_2440_, 2);
                                v_container_2488_ = crate::leanh::lean_ctor_get(v_x_2441_, 0);
                                crate::leanh::lean_inc(v_container_2488_);
                                v_content_2489_ = crate::leanh::lean_ctor_get(v_x_2441_, 1);
                                crate::leanh::lean_inc_ref(v_content_2489_);
                                crate::leanh::lean_dec_ref(v_x_2441_);
                                v___x_2490_ = crate::leanh::lean_apply_2(
                                    v_inst_2439_,
                                    v_container_2486_,
                                    v_container_2488_,
                                );
                                v___x_2491_ = (crate::leanh::lean_unbox(v___x_2490_) as u8);
                                if v___x_2491_ == 1 {
                                    v___x_2492_ = l_Array_compareLex___redArg(
                                        v___x_2451_,
                                        v_content_2487_,
                                        v_content_2489_,
                                    );
                                    crate::leanh::lean_dec_ref(v_content_2489_);
                                    crate::leanh::lean_dec_ref(v_content_2487_);
                                    if v___x_2492_ == 1 {
                                        return v___x_2492_;
                                    } else {
                                        return v___x_2492_;
                                    }
                                } else {
                                    crate::leanh::lean_dec_ref(v_content_2489_);
                                    crate::leanh::lean_dec_ref(v_content_2487_);
                                    crate::leanh::lean_dec_ref(v___x_2451_);
                                    v___x_2493_ = (crate::leanh::lean_unbox(v___x_2490_) as u8);
                                    return v___x_2493_;
                                }
                            }
                            _ => {
                                crate::leanh::lean_dec_ref(v___x_2451_);
                                crate::leanh::lean_dec_ref(v_inst_2439_);
                                v_string_2494_ = crate::leanh::lean_ctor_get(v_x_2440_, 0);
                                crate::leanh::lean_inc_ref(v_string_2494_);
                                crate::leanh::lean_dec_ref(v_x_2440_);
                                v_string_2495_ = crate::leanh::lean_ctor_get(v_x_2441_, 0);
                                crate::leanh::lean_inc_ref(v_string_2495_);
                                crate::leanh::lean_dec_ref(v_x_2441_);
                                v_string_2443_ = v_string_2494_;
                                v_string_x27_2444_ = v_string_2495_;
                                state = 1;
                                continue;
                            }
                        }
                    }
                } else {
                    crate::leanh::lean_dec(v___x_2447_);
                    crate::leanh::lean_dec(v___x_2446_);
                    crate::leanh::lean_dec_ref(v_x_2441_);
                    crate::leanh::lean_dec_ref(v_x_2440_);
                    crate::leanh::lean_dec_ref(v_inst_2439_);
                    v___x_2496_ = 0;
                    return v___x_2496_;
                }
            }
            1 => {
                v___x_2445_ = lean_string_compare(v_string_2443_, v_string_x27_2444_);
                crate::leanh::lean_dec_ref(v_string_x27_2444_);
                crate::leanh::lean_dec_ref(v_string_2443_);
                if v___x_2445_ == 1 {
                    return v___x_2445_;
                } else {
                    return v___x_2445_;
                }
            }
            2 => {
                v___x_2455_ =
                    l_Array_compareLex___redArg(v___x_2451_, v_content_2453_, v_content_x27_2454_);
                crate::leanh::lean_dec_ref(v_content_x27_2454_);
                crate::leanh::lean_dec_ref(v_content_2453_);
                if v___x_2455_ == 1 {
                    return v___x_2455_;
                } else {
                    return v___x_2455_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Doc_instOrdInline_ord(
    mut v_i_2497_: *mut crate::leanh::LeanObject,
    mut v_inst_2498_: *mut crate::leanh::LeanObject,
    mut v_x_2499_: *mut crate::leanh::LeanObject,
    mut v_x_2500_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_2501_: u8 = 0;
    v___x_2501_ = l_Lean_Doc_instOrdInline_ord___redArg(v_inst_2498_, v_x_2499_, v_x_2500_);
    return v___x_2501_;
}
pub unsafe fn l_Lean_Doc_instOrdInline_ord___boxed(
    mut v_i_2502_: *mut crate::leanh::LeanObject,
    mut v_inst_2503_: *mut crate::leanh::LeanObject,
    mut v_x_2504_: *mut crate::leanh::LeanObject,
    mut v_x_2505_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2506_: u8 = 0;
    let mut v_r_2507_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2506_ = l_Lean_Doc_instOrdInline_ord(v_i_2502_, v_inst_2503_, v_x_2504_, v_x_2505_);
    v_r_2507_ = crate::leanh::lean_box((v_res_2506_) as usize);
    return v_r_2507_;
}
pub unsafe fn l_Lean_Doc_instOrdInline___redArg(
    mut v_inst_2508_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2509_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2509_ = crate::leanh::lean_alloc_closure(
        l_Lean_Doc_instOrdInline_ord___boxed as *mut core::ffi::c_void,
        4,
        2,
    );
    crate::leanh::lean_closure_set(v___x_2509_, 0, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_2509_, 1, v_inst_2508_);
    return v___x_2509_;
}
pub unsafe fn l_Lean_Doc_instOrdInline(
    mut v_i_2510_: *mut crate::leanh::LeanObject,
    mut v_inst_2511_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2512_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2512_ = crate::leanh::lean_alloc_closure(
        l_Lean_Doc_instOrdInline_ord___boxed as *mut core::ffi::c_void,
        4,
        2,
    );
    crate::leanh::lean_closure_set(v___x_2512_, 0, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_2512_, 1, v_inst_2511_);
    return v___x_2512_;
}
pub unsafe fn l_Lean_Doc_instReprInline_repr___redArg___boxed(
    mut v_inst_2579_: *mut crate::leanh::LeanObject,
    mut v_x_2580_: *mut crate::leanh::LeanObject,
    mut v_prec_2581_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2582_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2582_ = l_Lean_Doc_instReprInline_repr___redArg(v_inst_2579_, v_x_2580_, v_prec_2581_);
    crate::leanh::lean_dec(v_prec_2581_);
    return v_res_2582_;
}
pub unsafe fn l_Lean_Doc_instReprInline_repr___redArg(
    mut v_inst_2583_: *mut crate::leanh::LeanObject,
    mut v_x_2584_: *mut crate::leanh::LeanObject,
    mut v_prec_2585_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_localinst_2586_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_string_2587_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2589_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2590_: u8 = 0;
    let mut v___y_2592_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2593_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2594_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2596_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2597_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2598_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2599_: u8 = 0;
    let mut v___x_2600_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2601_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2602_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2603_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2604_: u8 = 0;
    let mut v___x_2605_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2606_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2607_: u8 = 0;
    let mut v_content_2608_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2610_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2611_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2612_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2613_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2614_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2615_: u8 = 0;
    let mut v___x_2616_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2617_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2618_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2619_: u8 = 0;
    let mut v___x_2620_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2621_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_content_2622_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2624_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2625_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2626_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2627_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2628_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2629_: u8 = 0;
    let mut v___x_2630_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2631_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2632_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2633_: u8 = 0;
    let mut v___x_2634_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2635_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_string_2636_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2638_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2639_: u8 = 0;
    let mut v___y_2641_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2642_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2643_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2645_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2646_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2647_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2648_: u8 = 0;
    let mut v___x_2649_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2650_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2651_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2652_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2653_: u8 = 0;
    let mut v___x_2654_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2655_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2656_: u8 = 0;
    let mut v_mode_2657_: u8 = 0;
    let mut v_string_2658_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2660_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2661_: u8 = 0;
    let mut v___y_2663_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2664_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2665_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2666_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2667_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2668_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2669_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2670_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2671_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2672_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2673_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2674_: u8 = 0;
    let mut v___x_2676_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2677_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2678_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2679_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2680_: u8 = 0;
    let mut v___x_2681_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2682_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2683_: u8 = 0;
    let mut v_string_2684_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2686_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2687_: u8 = 0;
    let mut v___y_2689_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2690_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2691_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2693_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2694_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2695_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2696_: u8 = 0;
    let mut v___x_2697_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2698_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2699_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2700_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2701_: u8 = 0;
    let mut v___x_2702_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2703_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2704_: u8 = 0;
    let mut v_content_2705_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_url_2706_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2708_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2709_: u8 = 0;
    let mut v___y_2711_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2712_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2713_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2714_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2716_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2717_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2718_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2719_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2720_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2721_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2722_: u8 = 0;
    let mut v___x_2723_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2724_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2725_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2726_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2727_: u8 = 0;
    let mut v___x_2728_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2729_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2730_: u8 = 0;
    let mut v_name_2731_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_content_2732_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2734_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2735_: u8 = 0;
    let mut v___y_2737_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2738_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2739_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2740_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2741_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2743_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2744_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2745_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2746_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2747_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2748_: u8 = 0;
    let mut v___x_2749_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2750_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2751_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2752_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2753_: u8 = 0;
    let mut v___x_2754_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2755_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2756_: u8 = 0;
    let mut v_alt_2757_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_url_2758_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2760_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2761_: u8 = 0;
    let mut v___y_2763_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2764_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2765_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2766_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2767_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2769_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2770_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2771_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2772_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2773_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2774_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2775_: u8 = 0;
    let mut v___x_2776_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2777_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2778_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2779_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2780_: u8 = 0;
    let mut v___x_2781_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2782_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2783_: u8 = 0;
    let mut v_content_2784_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2786_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2787_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2788_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2789_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2790_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2791_: u8 = 0;
    let mut v___x_2792_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2793_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2794_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2795_: u8 = 0;
    let mut v___x_2796_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2797_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_container_2798_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_content_2799_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2801_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2802_: u8 = 0;
    let mut v___y_2804_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2805_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2806_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2807_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2808_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2810_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2811_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2812_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2813_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2814_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2815_: u8 = 0;
    let mut v___x_2816_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2817_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2818_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2819_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2820_: u8 = 0;
    let mut v___x_2821_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2822_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2823_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                crate::leanh::lean_inc_ref(v_inst_2583_);
                v_localinst_2586_ = crate::leanh::lean_alloc_closure(
                    l_Lean_Doc_instReprInline_repr___redArg___boxed as *mut core::ffi::c_void,
                    3,
                    1,
                );
                crate::leanh::lean_closure_set(v_localinst_2586_, 0, v_inst_2583_);
                match crate::leanh::lean_obj_tag(v_x_2584_) {
                    0 => {
                        crate::leanh::lean_dec_ref(v_localinst_2586_);
                        crate::leanh::lean_dec_ref(v_inst_2583_);
                        v_string_2587_ = crate::leanh::lean_ctor_get(v_x_2584_, 0);
                        v_isSharedCheck_2607_ = (!crate::leanh::lean_is_exclusive(v_x_2584_)) as u8;
                        if v_isSharedCheck_2607_ == 0 {
                            v___x_2589_ = v_x_2584_;
                            v_isShared_2590_ = v_isSharedCheck_2607_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_string_2587_);
                            crate::leanh::lean_dec(v_x_2584_);
                            v___x_2589_ = crate::leanh::lean_box(0);
                            v_isShared_2590_ = v_isSharedCheck_2607_;
                            state = 1;
                            continue;
                        }
                    }
                    1 => {
                        crate::leanh::lean_dec_ref(v_inst_2583_);
                        v_content_2608_ = crate::leanh::lean_ctor_get(v_x_2584_, 0);
                        crate::leanh::lean_inc_ref(v_content_2608_);
                        crate::leanh::lean_dec_ref_known(v_x_2584_, 1);
                        v___x_2618_ = crate::leanh::lean_unsigned_to_nat(1024);
                        v___x_2619_ = lean_nat_dec_le(v___x_2618_, v_prec_2585_);
                        if v___x_2619_ == 0 {
                            v___x_2620_ = crate::leanh::lean_obj_once(
                                core::ptr::addr_of_mut!(
                                    l_Lean_Doc_instReprMathMode_repr___closed__4
                                ),
                                core::ptr::addr_of_mut!(
                                    l_Lean_Doc_instReprMathMode_repr___closed__4_once
                                ),
                                _init_l_Lean_Doc_instReprMathMode_repr___closed__4,
                            );
                            v___y_2610_ = v___x_2620_;
                            state = 4;
                            continue;
                        } else {
                            v___x_2621_ = crate::leanh::lean_obj_once(
                                core::ptr::addr_of_mut!(
                                    l_Lean_Doc_instReprMathMode_repr___closed__5
                                ),
                                core::ptr::addr_of_mut!(
                                    l_Lean_Doc_instReprMathMode_repr___closed__5_once
                                ),
                                _init_l_Lean_Doc_instReprMathMode_repr___closed__5,
                            );
                            v___y_2610_ = v___x_2621_;
                            state = 4;
                            continue;
                        }
                    }
                    2 => {
                        crate::leanh::lean_dec_ref(v_inst_2583_);
                        v_content_2622_ = crate::leanh::lean_ctor_get(v_x_2584_, 0);
                        crate::leanh::lean_inc_ref(v_content_2622_);
                        crate::leanh::lean_dec_ref_known(v_x_2584_, 1);
                        v___x_2632_ = crate::leanh::lean_unsigned_to_nat(1024);
                        v___x_2633_ = lean_nat_dec_le(v___x_2632_, v_prec_2585_);
                        if v___x_2633_ == 0 {
                            v___x_2634_ = crate::leanh::lean_obj_once(
                                core::ptr::addr_of_mut!(
                                    l_Lean_Doc_instReprMathMode_repr___closed__4
                                ),
                                core::ptr::addr_of_mut!(
                                    l_Lean_Doc_instReprMathMode_repr___closed__4_once
                                ),
                                _init_l_Lean_Doc_instReprMathMode_repr___closed__4,
                            );
                            v___y_2624_ = v___x_2634_;
                            state = 5;
                            continue;
                        } else {
                            v___x_2635_ = crate::leanh::lean_obj_once(
                                core::ptr::addr_of_mut!(
                                    l_Lean_Doc_instReprMathMode_repr___closed__5
                                ),
                                core::ptr::addr_of_mut!(
                                    l_Lean_Doc_instReprMathMode_repr___closed__5_once
                                ),
                                _init_l_Lean_Doc_instReprMathMode_repr___closed__5,
                            );
                            v___y_2624_ = v___x_2635_;
                            state = 5;
                            continue;
                        }
                    }
                    3 => {
                        crate::leanh::lean_dec_ref(v_localinst_2586_);
                        crate::leanh::lean_dec_ref(v_inst_2583_);
                        v_string_2636_ = crate::leanh::lean_ctor_get(v_x_2584_, 0);
                        v_isSharedCheck_2656_ = (!crate::leanh::lean_is_exclusive(v_x_2584_)) as u8;
                        if v_isSharedCheck_2656_ == 0 {
                            v___x_2638_ = v_x_2584_;
                            v_isShared_2639_ = v_isSharedCheck_2656_;
                            state = 6;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_string_2636_);
                            crate::leanh::lean_dec(v_x_2584_);
                            v___x_2638_ = crate::leanh::lean_box(0);
                            v_isShared_2639_ = v_isSharedCheck_2656_;
                            state = 6;
                            continue;
                        }
                    }
                    4 => {
                        crate::leanh::lean_dec_ref(v_localinst_2586_);
                        crate::leanh::lean_dec_ref(v_inst_2583_);
                        v_mode_2657_ = crate::leanh::lean_ctor_get_uint8(
                            v_x_2584_,
                            (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                        );
                        v_string_2658_ = crate::leanh::lean_ctor_get(v_x_2584_, 0);
                        v_isSharedCheck_2683_ = (!crate::leanh::lean_is_exclusive(v_x_2584_)) as u8;
                        if v_isSharedCheck_2683_ == 0 {
                            v___x_2660_ = v_x_2584_;
                            v_isShared_2661_ = v_isSharedCheck_2683_;
                            state = 9;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_string_2658_);
                            crate::leanh::lean_dec(v_x_2584_);
                            v___x_2660_ = crate::leanh::lean_box(0);
                            v_isShared_2661_ = v_isSharedCheck_2683_;
                            state = 9;
                            continue;
                        }
                    }
                    5 => {
                        crate::leanh::lean_dec_ref(v_localinst_2586_);
                        crate::leanh::lean_dec_ref(v_inst_2583_);
                        v_string_2684_ = crate::leanh::lean_ctor_get(v_x_2584_, 0);
                        v_isSharedCheck_2704_ = (!crate::leanh::lean_is_exclusive(v_x_2584_)) as u8;
                        if v_isSharedCheck_2704_ == 0 {
                            v___x_2686_ = v_x_2584_;
                            v_isShared_2687_ = v_isSharedCheck_2704_;
                            state = 12;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_string_2684_);
                            crate::leanh::lean_dec(v_x_2584_);
                            v___x_2686_ = crate::leanh::lean_box(0);
                            v_isShared_2687_ = v_isSharedCheck_2704_;
                            state = 12;
                            continue;
                        }
                    }
                    6 => {
                        crate::leanh::lean_dec_ref(v_inst_2583_);
                        v_content_2705_ = crate::leanh::lean_ctor_get(v_x_2584_, 0);
                        v_url_2706_ = crate::leanh::lean_ctor_get(v_x_2584_, 1);
                        v_isSharedCheck_2730_ = (!crate::leanh::lean_is_exclusive(v_x_2584_)) as u8;
                        if v_isSharedCheck_2730_ == 0 {
                            v___x_2708_ = v_x_2584_;
                            v_isShared_2709_ = v_isSharedCheck_2730_;
                            state = 15;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_url_2706_);
                            crate::leanh::lean_inc(v_content_2705_);
                            crate::leanh::lean_dec(v_x_2584_);
                            v___x_2708_ = crate::leanh::lean_box(0);
                            v_isShared_2709_ = v_isSharedCheck_2730_;
                            state = 15;
                            continue;
                        }
                    }
                    7 => {
                        crate::leanh::lean_dec_ref(v_inst_2583_);
                        v_name_2731_ = crate::leanh::lean_ctor_get(v_x_2584_, 0);
                        v_content_2732_ = crate::leanh::lean_ctor_get(v_x_2584_, 1);
                        v_isSharedCheck_2756_ = (!crate::leanh::lean_is_exclusive(v_x_2584_)) as u8;
                        if v_isSharedCheck_2756_ == 0 {
                            v___x_2734_ = v_x_2584_;
                            v_isShared_2735_ = v_isSharedCheck_2756_;
                            state = 18;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_content_2732_);
                            crate::leanh::lean_inc(v_name_2731_);
                            crate::leanh::lean_dec(v_x_2584_);
                            v___x_2734_ = crate::leanh::lean_box(0);
                            v_isShared_2735_ = v_isSharedCheck_2756_;
                            state = 18;
                            continue;
                        }
                    }
                    8 => {
                        crate::leanh::lean_dec_ref(v_localinst_2586_);
                        crate::leanh::lean_dec_ref(v_inst_2583_);
                        v_alt_2757_ = crate::leanh::lean_ctor_get(v_x_2584_, 0);
                        v_url_2758_ = crate::leanh::lean_ctor_get(v_x_2584_, 1);
                        v_isSharedCheck_2783_ = (!crate::leanh::lean_is_exclusive(v_x_2584_)) as u8;
                        if v_isSharedCheck_2783_ == 0 {
                            v___x_2760_ = v_x_2584_;
                            v_isShared_2761_ = v_isSharedCheck_2783_;
                            state = 21;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_url_2758_);
                            crate::leanh::lean_inc(v_alt_2757_);
                            crate::leanh::lean_dec(v_x_2584_);
                            v___x_2760_ = crate::leanh::lean_box(0);
                            v_isShared_2761_ = v_isSharedCheck_2783_;
                            state = 21;
                            continue;
                        }
                    }
                    9 => {
                        crate::leanh::lean_dec_ref(v_inst_2583_);
                        v_content_2784_ = crate::leanh::lean_ctor_get(v_x_2584_, 0);
                        crate::leanh::lean_inc_ref(v_content_2784_);
                        crate::leanh::lean_dec_ref_known(v_x_2584_, 1);
                        v___x_2794_ = crate::leanh::lean_unsigned_to_nat(1024);
                        v___x_2795_ = lean_nat_dec_le(v___x_2794_, v_prec_2585_);
                        if v___x_2795_ == 0 {
                            v___x_2796_ = crate::leanh::lean_obj_once(
                                core::ptr::addr_of_mut!(
                                    l_Lean_Doc_instReprMathMode_repr___closed__4
                                ),
                                core::ptr::addr_of_mut!(
                                    l_Lean_Doc_instReprMathMode_repr___closed__4_once
                                ),
                                _init_l_Lean_Doc_instReprMathMode_repr___closed__4,
                            );
                            v___y_2786_ = v___x_2796_;
                            state = 24;
                            continue;
                        } else {
                            v___x_2797_ = crate::leanh::lean_obj_once(
                                core::ptr::addr_of_mut!(
                                    l_Lean_Doc_instReprMathMode_repr___closed__5
                                ),
                                core::ptr::addr_of_mut!(
                                    l_Lean_Doc_instReprMathMode_repr___closed__5_once
                                ),
                                _init_l_Lean_Doc_instReprMathMode_repr___closed__5,
                            );
                            v___y_2786_ = v___x_2797_;
                            state = 24;
                            continue;
                        }
                    }
                    _ => {
                        v_container_2798_ = crate::leanh::lean_ctor_get(v_x_2584_, 0);
                        v_content_2799_ = crate::leanh::lean_ctor_get(v_x_2584_, 1);
                        v_isSharedCheck_2823_ = (!crate::leanh::lean_is_exclusive(v_x_2584_)) as u8;
                        if v_isSharedCheck_2823_ == 0 {
                            v___x_2801_ = v_x_2584_;
                            v_isShared_2802_ = v_isSharedCheck_2823_;
                            state = 25;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_content_2799_);
                            crate::leanh::lean_inc(v_container_2798_);
                            crate::leanh::lean_dec(v_x_2584_);
                            v___x_2801_ = crate::leanh::lean_box(0);
                            v_isShared_2802_ = v_isSharedCheck_2823_;
                            state = 25;
                            continue;
                        }
                    }
                }
            }
            1 => {
                v___x_2603_ = crate::leanh::lean_unsigned_to_nat(1024);
                v___x_2604_ = lean_nat_dec_le(v___x_2603_, v_prec_2585_);
                if v___x_2604_ == 0 {
                    v___x_2605_ = crate::leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(l_Lean_Doc_instReprMathMode_repr___closed__4),
                        core::ptr::addr_of_mut!(l_Lean_Doc_instReprMathMode_repr___closed__4_once),
                        _init_l_Lean_Doc_instReprMathMode_repr___closed__4,
                    );
                    v___y_2592_ = v___x_2605_;
                    state = 2;
                    continue;
                } else {
                    v___x_2606_ = crate::leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(l_Lean_Doc_instReprMathMode_repr___closed__5),
                        core::ptr::addr_of_mut!(l_Lean_Doc_instReprMathMode_repr___closed__5_once),
                        _init_l_Lean_Doc_instReprMathMode_repr___closed__5,
                    );
                    v___y_2592_ = v___x_2606_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_2593_ = l_Lean_Doc_instReprInline_repr___redArg___closed__2;
                v___x_2594_ = l_String_quote(v_string_2587_);
                if v_isShared_2590_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_2589_, 3);
                    crate::leanh::lean_ctor_set(v___x_2589_, 0, v___x_2594_);
                    v___x_2596_ = v___x_2589_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_2602_ = crate::leanh::lean_alloc_ctor(3, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2602_, 0, v___x_2594_);
                    v___x_2596_ = v_reuseFailAlloc_2602_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_2597_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2597_, 0, v___x_2593_);
                crate::leanh::lean_ctor_set(v___x_2597_, 1, v___x_2596_);
                crate::leanh::lean_inc(v___y_2592_);
                v___x_2598_ = crate::leanh::lean_alloc_ctor(4, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2598_, 0, v___y_2592_);
                crate::leanh::lean_ctor_set(v___x_2598_, 1, v___x_2597_);
                v___x_2599_ = 0;
                v___x_2600_ = crate::leanh::lean_alloc_ctor(6, 1, (1) as u32);
                crate::leanh::lean_ctor_set(v___x_2600_, 0, v___x_2598_);
                crate::leanh::lean_ctor_set_uint8(
                    v___x_2600_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                    v___x_2599_,
                );
                v___x_2601_ = l_Repr_addAppParen(v___x_2600_, v_prec_2585_);
                return v___x_2601_;
            }
            4 => {
                v___x_2611_ = l_Lean_Doc_instReprInline_repr___redArg___closed__5;
                v___x_2612_ = l_Array_repr___redArg(v_localinst_2586_, v_content_2608_);
                v___x_2613_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2613_, 0, v___x_2611_);
                crate::leanh::lean_ctor_set(v___x_2613_, 1, v___x_2612_);
                crate::leanh::lean_inc(v___y_2610_);
                v___x_2614_ = crate::leanh::lean_alloc_ctor(4, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2614_, 0, v___y_2610_);
                crate::leanh::lean_ctor_set(v___x_2614_, 1, v___x_2613_);
                v___x_2615_ = 0;
                v___x_2616_ = crate::leanh::lean_alloc_ctor(6, 1, (1) as u32);
                crate::leanh::lean_ctor_set(v___x_2616_, 0, v___x_2614_);
                crate::leanh::lean_ctor_set_uint8(
                    v___x_2616_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                    v___x_2615_,
                );
                v___x_2617_ = l_Repr_addAppParen(v___x_2616_, v_prec_2585_);
                return v___x_2617_;
            }
            5 => {
                v___x_2625_ = l_Lean_Doc_instReprInline_repr___redArg___closed__8;
                v___x_2626_ = l_Array_repr___redArg(v_localinst_2586_, v_content_2622_);
                v___x_2627_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2627_, 0, v___x_2625_);
                crate::leanh::lean_ctor_set(v___x_2627_, 1, v___x_2626_);
                crate::leanh::lean_inc(v___y_2624_);
                v___x_2628_ = crate::leanh::lean_alloc_ctor(4, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2628_, 0, v___y_2624_);
                crate::leanh::lean_ctor_set(v___x_2628_, 1, v___x_2627_);
                v___x_2629_ = 0;
                v___x_2630_ = crate::leanh::lean_alloc_ctor(6, 1, (1) as u32);
                crate::leanh::lean_ctor_set(v___x_2630_, 0, v___x_2628_);
                crate::leanh::lean_ctor_set_uint8(
                    v___x_2630_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                    v___x_2629_,
                );
                v___x_2631_ = l_Repr_addAppParen(v___x_2630_, v_prec_2585_);
                return v___x_2631_;
            }
            6 => {
                v___x_2652_ = crate::leanh::lean_unsigned_to_nat(1024);
                v___x_2653_ = lean_nat_dec_le(v___x_2652_, v_prec_2585_);
                if v___x_2653_ == 0 {
                    v___x_2654_ = crate::leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(l_Lean_Doc_instReprMathMode_repr___closed__4),
                        core::ptr::addr_of_mut!(l_Lean_Doc_instReprMathMode_repr___closed__4_once),
                        _init_l_Lean_Doc_instReprMathMode_repr___closed__4,
                    );
                    v___y_2641_ = v___x_2654_;
                    state = 7;
                    continue;
                } else {
                    v___x_2655_ = crate::leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(l_Lean_Doc_instReprMathMode_repr___closed__5),
                        core::ptr::addr_of_mut!(l_Lean_Doc_instReprMathMode_repr___closed__5_once),
                        _init_l_Lean_Doc_instReprMathMode_repr___closed__5,
                    );
                    v___y_2641_ = v___x_2655_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                v___x_2642_ = l_Lean_Doc_instReprInline_repr___redArg___closed__11;
                v___x_2643_ = l_String_quote(v_string_2636_);
                if v_isShared_2639_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2638_, 0, v___x_2643_);
                    v___x_2645_ = v___x_2638_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_2651_ = crate::leanh::lean_alloc_ctor(3, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2651_, 0, v___x_2643_);
                    v___x_2645_ = v_reuseFailAlloc_2651_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                v___x_2646_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2646_, 0, v___x_2642_);
                crate::leanh::lean_ctor_set(v___x_2646_, 1, v___x_2645_);
                crate::leanh::lean_inc(v___y_2641_);
                v___x_2647_ = crate::leanh::lean_alloc_ctor(4, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2647_, 0, v___y_2641_);
                crate::leanh::lean_ctor_set(v___x_2647_, 1, v___x_2646_);
                v___x_2648_ = 0;
                v___x_2649_ = crate::leanh::lean_alloc_ctor(6, 1, (1) as u32);
                crate::leanh::lean_ctor_set(v___x_2649_, 0, v___x_2647_);
                crate::leanh::lean_ctor_set_uint8(
                    v___x_2649_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                    v___x_2648_,
                );
                v___x_2650_ = l_Repr_addAppParen(v___x_2649_, v_prec_2585_);
                return v___x_2650_;
            }
            9 => {
                v___x_2679_ = crate::leanh::lean_unsigned_to_nat(1024);
                v___x_2680_ = lean_nat_dec_le(v___x_2679_, v_prec_2585_);
                if v___x_2680_ == 0 {
                    v___x_2681_ = crate::leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(l_Lean_Doc_instReprMathMode_repr___closed__4),
                        core::ptr::addr_of_mut!(l_Lean_Doc_instReprMathMode_repr___closed__4_once),
                        _init_l_Lean_Doc_instReprMathMode_repr___closed__4,
                    );
                    v___y_2663_ = v___x_2681_;
                    state = 10;
                    continue;
                } else {
                    v___x_2682_ = crate::leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(l_Lean_Doc_instReprMathMode_repr___closed__5),
                        core::ptr::addr_of_mut!(l_Lean_Doc_instReprMathMode_repr___closed__5_once),
                        _init_l_Lean_Doc_instReprMathMode_repr___closed__5,
                    );
                    v___y_2663_ = v___x_2682_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                v___x_2664_ = crate::leanh::lean_box(1);
                v___x_2665_ = l_Lean_Doc_instReprInline_repr___redArg___closed__14;
                v___x_2666_ = crate::leanh::lean_unsigned_to_nat(1024);
                v___x_2667_ = l_Lean_Doc_instReprMathMode_repr(v_mode_2657_, v___x_2666_);
                v___x_2668_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2668_, 0, v___x_2665_);
                crate::leanh::lean_ctor_set(v___x_2668_, 1, v___x_2667_);
                v___x_2669_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2669_, 0, v___x_2668_);
                crate::leanh::lean_ctor_set(v___x_2669_, 1, v___x_2664_);
                v___x_2670_ = l_String_quote(v_string_2658_);
                v___x_2671_ = crate::leanh::lean_alloc_ctor(3, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2671_, 0, v___x_2670_);
                v___x_2672_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2672_, 0, v___x_2669_);
                crate::leanh::lean_ctor_set(v___x_2672_, 1, v___x_2671_);
                crate::leanh::lean_inc(v___y_2663_);
                v___x_2673_ = crate::leanh::lean_alloc_ctor(4, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2673_, 0, v___y_2663_);
                crate::leanh::lean_ctor_set(v___x_2673_, 1, v___x_2672_);
                v___x_2674_ = 0;
                if v_isShared_2661_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_2660_, 6);
                    crate::leanh::lean_ctor_set(v___x_2660_, 0, v___x_2673_);
                    v___x_2676_ = v___x_2660_;
                    state = 11;
                    continue;
                } else {
                    v_reuseFailAlloc_2678_ = crate::leanh::lean_alloc_ctor(6, 1, (1) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2678_, 0, v___x_2673_);
                    v___x_2676_ = v_reuseFailAlloc_2678_;
                    state = 11;
                    continue;
                }
            }
            11 => {
                crate::leanh::lean_ctor_set_uint8(
                    v___x_2676_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                    v___x_2674_,
                );
                v___x_2677_ = l_Repr_addAppParen(v___x_2676_, v_prec_2585_);
                return v___x_2677_;
            }
            12 => {
                v___x_2700_ = crate::leanh::lean_unsigned_to_nat(1024);
                v___x_2701_ = lean_nat_dec_le(v___x_2700_, v_prec_2585_);
                if v___x_2701_ == 0 {
                    v___x_2702_ = crate::leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(l_Lean_Doc_instReprMathMode_repr___closed__4),
                        core::ptr::addr_of_mut!(l_Lean_Doc_instReprMathMode_repr___closed__4_once),
                        _init_l_Lean_Doc_instReprMathMode_repr___closed__4,
                    );
                    v___y_2689_ = v___x_2702_;
                    state = 13;
                    continue;
                } else {
                    v___x_2703_ = crate::leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(l_Lean_Doc_instReprMathMode_repr___closed__5),
                        core::ptr::addr_of_mut!(l_Lean_Doc_instReprMathMode_repr___closed__5_once),
                        _init_l_Lean_Doc_instReprMathMode_repr___closed__5,
                    );
                    v___y_2689_ = v___x_2703_;
                    state = 13;
                    continue;
                }
            }
            13 => {
                v___x_2690_ = l_Lean_Doc_instReprInline_repr___redArg___closed__17;
                v___x_2691_ = l_String_quote(v_string_2684_);
                if v_isShared_2687_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_2686_, 3);
                    crate::leanh::lean_ctor_set(v___x_2686_, 0, v___x_2691_);
                    v___x_2693_ = v___x_2686_;
                    state = 14;
                    continue;
                } else {
                    v_reuseFailAlloc_2699_ = crate::leanh::lean_alloc_ctor(3, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2699_, 0, v___x_2691_);
                    v___x_2693_ = v_reuseFailAlloc_2699_;
                    state = 14;
                    continue;
                }
            }
            14 => {
                v___x_2694_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2694_, 0, v___x_2690_);
                crate::leanh::lean_ctor_set(v___x_2694_, 1, v___x_2693_);
                crate::leanh::lean_inc(v___y_2689_);
                v___x_2695_ = crate::leanh::lean_alloc_ctor(4, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2695_, 0, v___y_2689_);
                crate::leanh::lean_ctor_set(v___x_2695_, 1, v___x_2694_);
                v___x_2696_ = 0;
                v___x_2697_ = crate::leanh::lean_alloc_ctor(6, 1, (1) as u32);
                crate::leanh::lean_ctor_set(v___x_2697_, 0, v___x_2695_);
                crate::leanh::lean_ctor_set_uint8(
                    v___x_2697_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                    v___x_2696_,
                );
                v___x_2698_ = l_Repr_addAppParen(v___x_2697_, v_prec_2585_);
                return v___x_2698_;
            }
            15 => {
                v___x_2726_ = crate::leanh::lean_unsigned_to_nat(1024);
                v___x_2727_ = lean_nat_dec_le(v___x_2726_, v_prec_2585_);
                if v___x_2727_ == 0 {
                    v___x_2728_ = crate::leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(l_Lean_Doc_instReprMathMode_repr___closed__4),
                        core::ptr::addr_of_mut!(l_Lean_Doc_instReprMathMode_repr___closed__4_once),
                        _init_l_Lean_Doc_instReprMathMode_repr___closed__4,
                    );
                    v___y_2711_ = v___x_2728_;
                    state = 16;
                    continue;
                } else {
                    v___x_2729_ = crate::leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(l_Lean_Doc_instReprMathMode_repr___closed__5),
                        core::ptr::addr_of_mut!(l_Lean_Doc_instReprMathMode_repr___closed__5_once),
                        _init_l_Lean_Doc_instReprMathMode_repr___closed__5,
                    );
                    v___y_2711_ = v___x_2729_;
                    state = 16;
                    continue;
                }
            }
            16 => {
                v___x_2712_ = crate::leanh::lean_box(1);
                v___x_2713_ = l_Lean_Doc_instReprInline_repr___redArg___closed__20;
                v___x_2714_ = l_Array_repr___redArg(v_localinst_2586_, v_content_2705_);
                if v_isShared_2709_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_2708_, 5);
                    crate::leanh::lean_ctor_set(v___x_2708_, 1, v___x_2714_);
                    crate::leanh::lean_ctor_set(v___x_2708_, 0, v___x_2713_);
                    v___x_2716_ = v___x_2708_;
                    state = 17;
                    continue;
                } else {
                    v_reuseFailAlloc_2725_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2725_, 0, v___x_2713_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2725_, 1, v___x_2714_);
                    v___x_2716_ = v_reuseFailAlloc_2725_;
                    state = 17;
                    continue;
                }
            }
            17 => {
                v___x_2717_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2717_, 0, v___x_2716_);
                crate::leanh::lean_ctor_set(v___x_2717_, 1, v___x_2712_);
                v___x_2718_ = l_String_quote(v_url_2706_);
                v___x_2719_ = crate::leanh::lean_alloc_ctor(3, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2719_, 0, v___x_2718_);
                v___x_2720_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2720_, 0, v___x_2717_);
                crate::leanh::lean_ctor_set(v___x_2720_, 1, v___x_2719_);
                crate::leanh::lean_inc(v___y_2711_);
                v___x_2721_ = crate::leanh::lean_alloc_ctor(4, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2721_, 0, v___y_2711_);
                crate::leanh::lean_ctor_set(v___x_2721_, 1, v___x_2720_);
                v___x_2722_ = 0;
                v___x_2723_ = crate::leanh::lean_alloc_ctor(6, 1, (1) as u32);
                crate::leanh::lean_ctor_set(v___x_2723_, 0, v___x_2721_);
                crate::leanh::lean_ctor_set_uint8(
                    v___x_2723_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                    v___x_2722_,
                );
                v___x_2724_ = l_Repr_addAppParen(v___x_2723_, v_prec_2585_);
                return v___x_2724_;
            }
            18 => {
                v___x_2752_ = crate::leanh::lean_unsigned_to_nat(1024);
                v___x_2753_ = lean_nat_dec_le(v___x_2752_, v_prec_2585_);
                if v___x_2753_ == 0 {
                    v___x_2754_ = crate::leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(l_Lean_Doc_instReprMathMode_repr___closed__4),
                        core::ptr::addr_of_mut!(l_Lean_Doc_instReprMathMode_repr___closed__4_once),
                        _init_l_Lean_Doc_instReprMathMode_repr___closed__4,
                    );
                    v___y_2737_ = v___x_2754_;
                    state = 19;
                    continue;
                } else {
                    v___x_2755_ = crate::leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(l_Lean_Doc_instReprMathMode_repr___closed__5),
                        core::ptr::addr_of_mut!(l_Lean_Doc_instReprMathMode_repr___closed__5_once),
                        _init_l_Lean_Doc_instReprMathMode_repr___closed__5,
                    );
                    v___y_2737_ = v___x_2755_;
                    state = 19;
                    continue;
                }
            }
            19 => {
                v___x_2738_ = crate::leanh::lean_box(1);
                v___x_2739_ = l_Lean_Doc_instReprInline_repr___redArg___closed__23;
                v___x_2740_ = l_String_quote(v_name_2731_);
                v___x_2741_ = crate::leanh::lean_alloc_ctor(3, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2741_, 0, v___x_2740_);
                if v_isShared_2735_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_2734_, 5);
                    crate::leanh::lean_ctor_set(v___x_2734_, 1, v___x_2741_);
                    crate::leanh::lean_ctor_set(v___x_2734_, 0, v___x_2739_);
                    v___x_2743_ = v___x_2734_;
                    state = 20;
                    continue;
                } else {
                    v_reuseFailAlloc_2751_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2751_, 0, v___x_2739_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2751_, 1, v___x_2741_);
                    v___x_2743_ = v_reuseFailAlloc_2751_;
                    state = 20;
                    continue;
                }
            }
            20 => {
                v___x_2744_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2744_, 0, v___x_2743_);
                crate::leanh::lean_ctor_set(v___x_2744_, 1, v___x_2738_);
                v___x_2745_ = l_Array_repr___redArg(v_localinst_2586_, v_content_2732_);
                v___x_2746_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2746_, 0, v___x_2744_);
                crate::leanh::lean_ctor_set(v___x_2746_, 1, v___x_2745_);
                crate::leanh::lean_inc(v___y_2737_);
                v___x_2747_ = crate::leanh::lean_alloc_ctor(4, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2747_, 0, v___y_2737_);
                crate::leanh::lean_ctor_set(v___x_2747_, 1, v___x_2746_);
                v___x_2748_ = 0;
                v___x_2749_ = crate::leanh::lean_alloc_ctor(6, 1, (1) as u32);
                crate::leanh::lean_ctor_set(v___x_2749_, 0, v___x_2747_);
                crate::leanh::lean_ctor_set_uint8(
                    v___x_2749_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                    v___x_2748_,
                );
                v___x_2750_ = l_Repr_addAppParen(v___x_2749_, v_prec_2585_);
                return v___x_2750_;
            }
            21 => {
                v___x_2779_ = crate::leanh::lean_unsigned_to_nat(1024);
                v___x_2780_ = lean_nat_dec_le(v___x_2779_, v_prec_2585_);
                if v___x_2780_ == 0 {
                    v___x_2781_ = crate::leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(l_Lean_Doc_instReprMathMode_repr___closed__4),
                        core::ptr::addr_of_mut!(l_Lean_Doc_instReprMathMode_repr___closed__4_once),
                        _init_l_Lean_Doc_instReprMathMode_repr___closed__4,
                    );
                    v___y_2763_ = v___x_2781_;
                    state = 22;
                    continue;
                } else {
                    v___x_2782_ = crate::leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(l_Lean_Doc_instReprMathMode_repr___closed__5),
                        core::ptr::addr_of_mut!(l_Lean_Doc_instReprMathMode_repr___closed__5_once),
                        _init_l_Lean_Doc_instReprMathMode_repr___closed__5,
                    );
                    v___y_2763_ = v___x_2782_;
                    state = 22;
                    continue;
                }
            }
            22 => {
                v___x_2764_ = crate::leanh::lean_box(1);
                v___x_2765_ = l_Lean_Doc_instReprInline_repr___redArg___closed__26;
                v___x_2766_ = l_String_quote(v_alt_2757_);
                v___x_2767_ = crate::leanh::lean_alloc_ctor(3, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2767_, 0, v___x_2766_);
                if v_isShared_2761_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_2760_, 5);
                    crate::leanh::lean_ctor_set(v___x_2760_, 1, v___x_2767_);
                    crate::leanh::lean_ctor_set(v___x_2760_, 0, v___x_2765_);
                    v___x_2769_ = v___x_2760_;
                    state = 23;
                    continue;
                } else {
                    v_reuseFailAlloc_2778_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2778_, 0, v___x_2765_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2778_, 1, v___x_2767_);
                    v___x_2769_ = v_reuseFailAlloc_2778_;
                    state = 23;
                    continue;
                }
            }
            23 => {
                v___x_2770_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2770_, 0, v___x_2769_);
                crate::leanh::lean_ctor_set(v___x_2770_, 1, v___x_2764_);
                v___x_2771_ = l_String_quote(v_url_2758_);
                v___x_2772_ = crate::leanh::lean_alloc_ctor(3, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2772_, 0, v___x_2771_);
                v___x_2773_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2773_, 0, v___x_2770_);
                crate::leanh::lean_ctor_set(v___x_2773_, 1, v___x_2772_);
                crate::leanh::lean_inc(v___y_2763_);
                v___x_2774_ = crate::leanh::lean_alloc_ctor(4, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2774_, 0, v___y_2763_);
                crate::leanh::lean_ctor_set(v___x_2774_, 1, v___x_2773_);
                v___x_2775_ = 0;
                v___x_2776_ = crate::leanh::lean_alloc_ctor(6, 1, (1) as u32);
                crate::leanh::lean_ctor_set(v___x_2776_, 0, v___x_2774_);
                crate::leanh::lean_ctor_set_uint8(
                    v___x_2776_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                    v___x_2775_,
                );
                v___x_2777_ = l_Repr_addAppParen(v___x_2776_, v_prec_2585_);
                return v___x_2777_;
            }
            24 => {
                v___x_2787_ = l_Lean_Doc_instReprInline_repr___redArg___closed__29;
                v___x_2788_ = l_Array_repr___redArg(v_localinst_2586_, v_content_2784_);
                v___x_2789_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2789_, 0, v___x_2787_);
                crate::leanh::lean_ctor_set(v___x_2789_, 1, v___x_2788_);
                crate::leanh::lean_inc(v___y_2786_);
                v___x_2790_ = crate::leanh::lean_alloc_ctor(4, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2790_, 0, v___y_2786_);
                crate::leanh::lean_ctor_set(v___x_2790_, 1, v___x_2789_);
                v___x_2791_ = 0;
                v___x_2792_ = crate::leanh::lean_alloc_ctor(6, 1, (1) as u32);
                crate::leanh::lean_ctor_set(v___x_2792_, 0, v___x_2790_);
                crate::leanh::lean_ctor_set_uint8(
                    v___x_2792_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                    v___x_2791_,
                );
                v___x_2793_ = l_Repr_addAppParen(v___x_2792_, v_prec_2585_);
                return v___x_2793_;
            }
            25 => {
                v___x_2819_ = crate::leanh::lean_unsigned_to_nat(1024);
                v___x_2820_ = lean_nat_dec_le(v___x_2819_, v_prec_2585_);
                if v___x_2820_ == 0 {
                    v___x_2821_ = crate::leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(l_Lean_Doc_instReprMathMode_repr___closed__4),
                        core::ptr::addr_of_mut!(l_Lean_Doc_instReprMathMode_repr___closed__4_once),
                        _init_l_Lean_Doc_instReprMathMode_repr___closed__4,
                    );
                    v___y_2804_ = v___x_2821_;
                    state = 26;
                    continue;
                } else {
                    v___x_2822_ = crate::leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(l_Lean_Doc_instReprMathMode_repr___closed__5),
                        core::ptr::addr_of_mut!(l_Lean_Doc_instReprMathMode_repr___closed__5_once),
                        _init_l_Lean_Doc_instReprMathMode_repr___closed__5,
                    );
                    v___y_2804_ = v___x_2822_;
                    state = 26;
                    continue;
                }
            }
            26 => {
                v___x_2805_ = crate::leanh::lean_box(1);
                v___x_2806_ = l_Lean_Doc_instReprInline_repr___redArg___closed__32;
                v___x_2807_ = crate::leanh::lean_unsigned_to_nat(1024);
                v___x_2808_ =
                    crate::leanh::lean_apply_2(v_inst_2583_, v_container_2798_, v___x_2807_);
                if v_isShared_2802_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_2801_, 5);
                    crate::leanh::lean_ctor_set(v___x_2801_, 1, v___x_2808_);
                    crate::leanh::lean_ctor_set(v___x_2801_, 0, v___x_2806_);
                    v___x_2810_ = v___x_2801_;
                    state = 27;
                    continue;
                } else {
                    v_reuseFailAlloc_2818_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2818_, 0, v___x_2806_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2818_, 1, v___x_2808_);
                    v___x_2810_ = v_reuseFailAlloc_2818_;
                    state = 27;
                    continue;
                }
            }
            27 => {
                v___x_2811_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2811_, 0, v___x_2810_);
                crate::leanh::lean_ctor_set(v___x_2811_, 1, v___x_2805_);
                v___x_2812_ = l_Array_repr___redArg(v_localinst_2586_, v_content_2799_);
                v___x_2813_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2813_, 0, v___x_2811_);
                crate::leanh::lean_ctor_set(v___x_2813_, 1, v___x_2812_);
                crate::leanh::lean_inc(v___y_2804_);
                v___x_2814_ = crate::leanh::lean_alloc_ctor(4, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2814_, 0, v___y_2804_);
                crate::leanh::lean_ctor_set(v___x_2814_, 1, v___x_2813_);
                v___x_2815_ = 0;
                v___x_2816_ = crate::leanh::lean_alloc_ctor(6, 1, (1) as u32);
                crate::leanh::lean_ctor_set(v___x_2816_, 0, v___x_2814_);
                crate::leanh::lean_ctor_set_uint8(
                    v___x_2816_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                    v___x_2815_,
                );
                v___x_2817_ = l_Repr_addAppParen(v___x_2816_, v_prec_2585_);
                return v___x_2817_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Doc_instReprInline_repr(
    mut v_i_2824_: *mut crate::leanh::LeanObject,
    mut v_inst_2825_: *mut crate::leanh::LeanObject,
    mut v_x_2826_: *mut crate::leanh::LeanObject,
    mut v_prec_2827_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2828_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2828_ = l_Lean_Doc_instReprInline_repr___redArg(v_inst_2825_, v_x_2826_, v_prec_2827_);
    return v___x_2828_;
}
pub unsafe fn l_Lean_Doc_instReprInline_repr___boxed(
    mut v_i_2829_: *mut crate::leanh::LeanObject,
    mut v_inst_2830_: *mut crate::leanh::LeanObject,
    mut v_x_2831_: *mut crate::leanh::LeanObject,
    mut v_prec_2832_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2833_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2833_ = l_Lean_Doc_instReprInline_repr(v_i_2829_, v_inst_2830_, v_x_2831_, v_prec_2832_);
    crate::leanh::lean_dec(v_prec_2832_);
    return v_res_2833_;
}
pub unsafe fn l_Lean_Doc_instReprInline___redArg(
    mut v_inst_2834_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2835_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2835_ = crate::leanh::lean_alloc_closure(
        l_Lean_Doc_instReprInline_repr___boxed as *mut core::ffi::c_void,
        4,
        2,
    );
    crate::leanh::lean_closure_set(v___x_2835_, 0, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_2835_, 1, v_inst_2834_);
    return v___x_2835_;
}
pub unsafe fn l_Lean_Doc_instReprInline(
    mut v_i_2836_: *mut crate::leanh::LeanObject,
    mut v_inst_2837_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2838_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2838_ = crate::leanh::lean_alloc_closure(
        l_Lean_Doc_instReprInline_repr___boxed as *mut core::ffi::c_void,
        4,
        2,
    );
    crate::leanh::lean_closure_set(v___x_2838_, 0, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_2838_, 1, v_inst_2837_);
    return v___x_2838_;
}
pub unsafe fn l_Lean_Doc_instInhabitedInline_default(
    mut v_i_2842_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2843_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2843_ = l_Lean_Doc_instInhabitedInline_default___closed__1;
    return v___x_2843_;
}
pub unsafe fn _init_l_Lean_Doc_instInhabitedInline___closed__0() -> *mut crate::leanh::LeanObject {
    let mut v___x_2844_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2844_ = l_Lean_Doc_instInhabitedInline_default(crate::leanh::lean_box(0));
    return v___x_2844_;
}
pub unsafe fn l_Lean_Doc_instInhabitedInline(
    mut v_a_2845_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2846_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2846_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Doc_instInhabitedInline___closed__0),
        core::ptr::addr_of_mut!(l_Lean_Doc_instInhabitedInline___closed__0_once),
        _init_l_Lean_Doc_instInhabitedInline___closed__0,
    );
    return v___x_2846_;
}
pub unsafe fn l_Lean_Doc_Inline_cast___redArg(
    mut v_x_2847_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc_ref(v_x_2847_);
    return v_x_2847_;
}
pub unsafe fn l_Lean_Doc_Inline_cast___redArg___boxed(
    mut v_x_2848_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2849_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2849_ = l_Lean_Doc_Inline_cast___redArg(v_x_2848_);
    crate::leanh::lean_dec_ref(v_x_2848_);
    return v_res_2849_;
}
pub unsafe fn l_Lean_Doc_Inline_cast(
    mut v_i_2850_: *mut crate::leanh::LeanObject,
    mut v_i_x27_2851_: *mut crate::leanh::LeanObject,
    mut v_inlines__eq_2852_: *mut crate::leanh::LeanObject,
    mut v_x_2853_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc_ref(v_x_2853_);
    return v_x_2853_;
}
pub unsafe fn l_Lean_Doc_Inline_cast___boxed(
    mut v_i_2854_: *mut crate::leanh::LeanObject,
    mut v_i_x27_2855_: *mut crate::leanh::LeanObject,
    mut v_inlines__eq_2856_: *mut crate::leanh::LeanObject,
    mut v_x_2857_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2858_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2858_ = l_Lean_Doc_Inline_cast(v_i_2854_, v_i_x27_2855_, v_inlines__eq_2856_, v_x_2857_);
    crate::leanh::lean_dec_ref(v_x_2857_);
    return v_res_2858_;
}
pub unsafe fn l_Lean_Doc_instAppendInline___lam__0(
    mut v_x_2859_: *mut crate::leanh::LeanObject,
    mut v_x_2860_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_content_2861_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2862_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2863_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2864_: u8 = 0;
    let mut v_content_2865_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2867_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2868_: u8 = 0;
    let mut v___x_2869_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2870_: u8 = 0;
    let mut v___x_2871_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2873_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2874_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2875_: u8 = 0;
    let mut v___x_2877_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2878_: u8 = 0;
    let mut v___x_2879_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2881_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2882_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2883_: u8 = 0;
    let mut v_unused_2884_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_content_2885_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2887_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2888_: u8 = 0;
    let mut v___x_2889_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2890_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2891_: u8 = 0;
    let mut v___x_2892_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2893_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2894_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2895_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2897_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2898_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2899_: u8 = 0;
    let mut v___x_2900_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2901_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2902_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2903_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2904_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_2859_) == 9 {
                    v_content_2861_ = crate::leanh::lean_ctor_get(v_x_2859_, 0);
                    v___x_2862_ = lean_array_get_size(v_content_2861_);
                    v___x_2863_ = crate::leanh::lean_unsigned_to_nat(0);
                    v___x_2864_ = lean_nat_dec_eq(v___x_2862_, v___x_2863_);
                    if v___x_2864_ == 0 {
                        if crate::leanh::lean_obj_tag(v_x_2860_) == 9 {
                            v_content_2865_ = crate::leanh::lean_ctor_get(v_x_2860_, 0);
                            v_isSharedCheck_2875_ =
                                (!crate::leanh::lean_is_exclusive(v_x_2860_)) as u8;
                            if v_isSharedCheck_2875_ == 0 {
                                v___x_2867_ = v_x_2860_;
                                v_isShared_2868_ = v_isSharedCheck_2875_;
                                state = 1;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_content_2865_);
                                crate::leanh::lean_dec(v_x_2860_);
                                v___x_2867_ = crate::leanh::lean_box(0);
                                v_isShared_2868_ = v_isSharedCheck_2875_;
                                state = 1;
                                continue;
                            }
                        } else {
                            crate::leanh::lean_inc_ref(v_content_2861_);
                            v_isSharedCheck_2883_ =
                                (!crate::leanh::lean_is_exclusive(v_x_2859_)) as u8;
                            if v_isSharedCheck_2883_ == 0 {
                                v_unused_2884_ = crate::leanh::lean_ctor_get(v_x_2859_, 0);
                                crate::leanh::lean_dec(v_unused_2884_);
                                v___x_2877_ = v_x_2859_;
                                v_isShared_2878_ = v_isSharedCheck_2883_;
                                state = 3;
                                continue;
                            } else {
                                crate::leanh::lean_dec(v_x_2859_);
                                v___x_2877_ = crate::leanh::lean_box(0);
                                v_isShared_2878_ = v_isSharedCheck_2883_;
                                state = 3;
                                continue;
                            }
                        }
                    } else {
                        crate::leanh::lean_dec_ref_known(v_x_2859_, 1);
                        return v_x_2860_;
                    }
                } else {
                    if crate::leanh::lean_obj_tag(v_x_2860_) == 9 {
                        v_content_2885_ = crate::leanh::lean_ctor_get(v_x_2860_, 0);
                        v_isSharedCheck_2899_ = (!crate::leanh::lean_is_exclusive(v_x_2860_)) as u8;
                        if v_isSharedCheck_2899_ == 0 {
                            v___x_2887_ = v_x_2860_;
                            v_isShared_2888_ = v_isSharedCheck_2899_;
                            state = 5;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_content_2885_);
                            crate::leanh::lean_dec(v_x_2860_);
                            v___x_2887_ = crate::leanh::lean_box(0);
                            v_isShared_2888_ = v_isSharedCheck_2899_;
                            state = 5;
                            continue;
                        }
                    } else {
                        v___x_2900_ = crate::leanh::lean_unsigned_to_nat(2);
                        v___x_2901_ = lean_mk_empty_array_with_capacity(v___x_2900_);
                        v___x_2902_ = lean_array_push(v___x_2901_, v_x_2859_);
                        v___x_2903_ = lean_array_push(v___x_2902_, v_x_2860_);
                        v___x_2904_ = crate::leanh::lean_alloc_ctor(9, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_2904_, 0, v___x_2903_);
                        return v___x_2904_;
                    }
                }
            }
            1 => {
                v___x_2869_ = lean_array_get_size(v_content_2865_);
                v___x_2870_ = lean_nat_dec_eq(v___x_2869_, v___x_2863_);
                if v___x_2870_ == 0 {
                    crate::leanh::lean_inc_ref(v_content_2861_);
                    crate::leanh::lean_dec_ref_known(v_x_2859_, 1);
                    v___x_2871_ = l_Array_append___redArg(v_content_2861_, v_content_2865_);
                    crate::leanh::lean_dec_ref(v_content_2865_);
                    if v_isShared_2868_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_2867_, 0, v___x_2871_);
                        v___x_2873_ = v___x_2867_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_2874_ = crate::leanh::lean_alloc_ctor(9, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2874_, 0, v___x_2871_);
                        v___x_2873_ = v_reuseFailAlloc_2874_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_2867_);
                    crate::leanh::lean_dec_ref(v_content_2865_);
                    return v_x_2859_;
                }
            }
            2 => {
                return v___x_2873_;
            }
            3 => {
                v___x_2879_ = lean_array_push(v_content_2861_, v_x_2860_);
                if v_isShared_2878_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2877_, 0, v___x_2879_);
                    v___x_2881_ = v___x_2877_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2882_ = crate::leanh::lean_alloc_ctor(9, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2882_, 0, v___x_2879_);
                    v___x_2881_ = v_reuseFailAlloc_2882_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_2881_;
            }
            5 => {
                v___x_2889_ = lean_array_get_size(v_content_2885_);
                v___x_2890_ = crate::leanh::lean_unsigned_to_nat(0);
                v___x_2891_ = lean_nat_dec_eq(v___x_2889_, v___x_2890_);
                if v___x_2891_ == 0 {
                    v___x_2892_ = crate::leanh::lean_unsigned_to_nat(1);
                    v___x_2893_ = lean_mk_empty_array_with_capacity(v___x_2892_);
                    v___x_2894_ = lean_array_push(v___x_2893_, v_x_2859_);
                    v___x_2895_ = l_Array_append___redArg(v___x_2894_, v_content_2885_);
                    crate::leanh::lean_dec_ref(v_content_2885_);
                    if v_isShared_2888_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_2887_, 0, v___x_2895_);
                        v___x_2897_ = v___x_2887_;
                        state = 6;
                        continue;
                    } else {
                        v_reuseFailAlloc_2898_ = crate::leanh::lean_alloc_ctor(9, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2898_, 0, v___x_2895_);
                        v___x_2897_ = v_reuseFailAlloc_2898_;
                        state = 6;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_2887_);
                    crate::leanh::lean_dec_ref(v_content_2885_);
                    return v_x_2859_;
                }
            }
            6 => {
                return v___x_2897_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Doc_instAppendInline(
    mut v_i_2906_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_2907_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_2907_ = l_Lean_Doc_instAppendInline___closed__0;
    return v___f_2907_;
}
pub unsafe fn l_Lean_Doc_Inline_empty(
    mut v_i_2912_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2913_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2913_ = l_Lean_Doc_Inline_empty___closed__1;
    return v___x_2913_;
}
pub unsafe fn _init_l_Lean_Doc_instReprListItem_repr___redArg___closed__7()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2927_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2928_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2927_ = crate::leanh::lean_unsigned_to_nat(12);
    v___x_2928_ = lean_nat_to_int(v___x_2927_);
    return v___x_2928_;
}
pub unsafe fn _init_l_Lean_Doc_instReprListItem_repr___redArg___closed__9()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2930_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2931_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2930_ = l_Lean_Doc_instReprListItem_repr___redArg___closed__0;
    v___x_2931_ = lean_string_length(v___x_2930_);
    return v___x_2931_;
}
pub unsafe fn _init_l_Lean_Doc_instReprListItem_repr___redArg___closed__10()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2932_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2933_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2932_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Doc_instReprListItem_repr___redArg___closed__9),
        core::ptr::addr_of_mut!(l_Lean_Doc_instReprListItem_repr___redArg___closed__9_once),
        _init_l_Lean_Doc_instReprListItem_repr___redArg___closed__9,
    );
    v___x_2933_ = lean_nat_to_int(v___x_2932_);
    return v___x_2933_;
}
pub unsafe fn l_Lean_Doc_instReprListItem_repr___redArg(
    mut v_inst_2938_: *mut crate::leanh::LeanObject,
    mut v_x_2939_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2940_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2941_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2942_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2943_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2944_: u8 = 0;
    let mut v___x_2945_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2946_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2947_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2948_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2949_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2950_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2951_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2952_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2953_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2940_ = l_Lean_Doc_instReprListItem_repr___redArg___closed__6;
    v___x_2941_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Doc_instReprListItem_repr___redArg___closed__7),
        core::ptr::addr_of_mut!(l_Lean_Doc_instReprListItem_repr___redArg___closed__7_once),
        _init_l_Lean_Doc_instReprListItem_repr___redArg___closed__7,
    );
    v___x_2942_ = l_Array_repr___redArg(v_inst_2938_, v_x_2939_);
    v___x_2943_ = crate::leanh::lean_alloc_ctor(4, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2943_, 0, v___x_2941_);
    crate::leanh::lean_ctor_set(v___x_2943_, 1, v___x_2942_);
    v___x_2944_ = 0;
    v___x_2945_ = crate::leanh::lean_alloc_ctor(6, 1, (1) as u32);
    crate::leanh::lean_ctor_set(v___x_2945_, 0, v___x_2943_);
    crate::leanh::lean_ctor_set_uint8(
        v___x_2945_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
        v___x_2944_,
    );
    v___x_2946_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2946_, 0, v___x_2940_);
    crate::leanh::lean_ctor_set(v___x_2946_, 1, v___x_2945_);
    v___x_2947_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Doc_instReprListItem_repr___redArg___closed__10),
        core::ptr::addr_of_mut!(l_Lean_Doc_instReprListItem_repr___redArg___closed__10_once),
        _init_l_Lean_Doc_instReprListItem_repr___redArg___closed__10,
    );
    v___x_2948_ = l_Lean_Doc_instReprListItem_repr___redArg___closed__11;
    v___x_2949_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2949_, 0, v___x_2948_);
    crate::leanh::lean_ctor_set(v___x_2949_, 1, v___x_2946_);
    v___x_2950_ = l_Lean_Doc_instReprListItem_repr___redArg___closed__12;
    v___x_2951_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2951_, 0, v___x_2949_);
    crate::leanh::lean_ctor_set(v___x_2951_, 1, v___x_2950_);
    v___x_2952_ = crate::leanh::lean_alloc_ctor(4, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2952_, 0, v___x_2947_);
    crate::leanh::lean_ctor_set(v___x_2952_, 1, v___x_2951_);
    v___x_2953_ = crate::leanh::lean_alloc_ctor(6, 1, (1) as u32);
    crate::leanh::lean_ctor_set(v___x_2953_, 0, v___x_2952_);
    crate::leanh::lean_ctor_set_uint8(
        v___x_2953_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
        v___x_2944_,
    );
    return v___x_2953_;
}
pub unsafe fn l_Lean_Doc_instReprListItem_repr(
    mut v_00_u03b1_2954_: *mut crate::leanh::LeanObject,
    mut v_inst_2955_: *mut crate::leanh::LeanObject,
    mut v_x_2956_: *mut crate::leanh::LeanObject,
    mut v_prec_2957_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2958_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2958_ = l_Lean_Doc_instReprListItem_repr___redArg(v_inst_2955_, v_x_2956_);
    return v___x_2958_;
}
pub unsafe fn l_Lean_Doc_instReprListItem_repr___boxed(
    mut v_00_u03b1_2959_: *mut crate::leanh::LeanObject,
    mut v_inst_2960_: *mut crate::leanh::LeanObject,
    mut v_x_2961_: *mut crate::leanh::LeanObject,
    mut v_prec_2962_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2963_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2963_ =
        l_Lean_Doc_instReprListItem_repr(v_00_u03b1_2959_, v_inst_2960_, v_x_2961_, v_prec_2962_);
    crate::leanh::lean_dec(v_prec_2962_);
    return v_res_2963_;
}
pub unsafe fn l_Lean_Doc_instReprListItem___redArg(
    mut v_inst_2964_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2965_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2965_ = crate::leanh::lean_alloc_closure(
        l_Lean_Doc_instReprListItem_repr___boxed as *mut core::ffi::c_void,
        4,
        2,
    );
    crate::leanh::lean_closure_set(v___x_2965_, 0, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_2965_, 1, v_inst_2964_);
    return v___x_2965_;
}
pub unsafe fn l_Lean_Doc_instReprListItem(
    mut v_00_u03b1_2966_: *mut crate::leanh::LeanObject,
    mut v_inst_2967_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2968_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2968_ = crate::leanh::lean_alloc_closure(
        l_Lean_Doc_instReprListItem_repr___boxed as *mut core::ffi::c_void,
        4,
        2,
    );
    crate::leanh::lean_closure_set(v___x_2968_, 0, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_2968_, 1, v_inst_2967_);
    return v___x_2968_;
}
pub unsafe fn l_Lean_Doc_instBEqListItem_beq___redArg(
    mut v_inst_2969_: *mut crate::leanh::LeanObject,
    mut v_x_2970_: *mut crate::leanh::LeanObject,
    mut v_x_2971_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_2972_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2973_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2974_: u8 = 0;
    v___x_2972_ = lean_array_get_size(v_x_2970_);
    v___x_2973_ = lean_array_get_size(v_x_2971_);
    v___x_2974_ = lean_nat_dec_eq(v___x_2972_, v___x_2973_);
    if v___x_2974_ == 0 {
        crate::leanh::lean_dec_ref(v_inst_2969_);
        return v___x_2974_;
    } else {
        let mut v___x_2975_: u8 = 0;
        v___x_2975_ = l_Array_isEqvAux___redArg(v_x_2970_, v_x_2971_, v_inst_2969_, v___x_2972_);
        return v___x_2975_;
    }
}
pub unsafe fn l_Lean_Doc_instBEqListItem_beq___redArg___boxed(
    mut v_inst_2976_: *mut crate::leanh::LeanObject,
    mut v_x_2977_: *mut crate::leanh::LeanObject,
    mut v_x_2978_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2979_: u8 = 0;
    let mut v_r_2980_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2979_ = l_Lean_Doc_instBEqListItem_beq___redArg(v_inst_2976_, v_x_2977_, v_x_2978_);
    crate::leanh::lean_dec_ref(v_x_2978_);
    crate::leanh::lean_dec_ref(v_x_2977_);
    v_r_2980_ = crate::leanh::lean_box((v_res_2979_) as usize);
    return v_r_2980_;
}
pub unsafe fn l_Lean_Doc_instBEqListItem_beq(
    mut v_00_u03b1_2981_: *mut crate::leanh::LeanObject,
    mut v_inst_2982_: *mut crate::leanh::LeanObject,
    mut v_x_2983_: *mut crate::leanh::LeanObject,
    mut v_x_2984_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_2985_: u8 = 0;
    v___x_2985_ = l_Lean_Doc_instBEqListItem_beq___redArg(v_inst_2982_, v_x_2983_, v_x_2984_);
    return v___x_2985_;
}
pub unsafe fn l_Lean_Doc_instBEqListItem_beq___boxed(
    mut v_00_u03b1_2986_: *mut crate::leanh::LeanObject,
    mut v_inst_2987_: *mut crate::leanh::LeanObject,
    mut v_x_2988_: *mut crate::leanh::LeanObject,
    mut v_x_2989_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2990_: u8 = 0;
    let mut v_r_2991_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2990_ =
        l_Lean_Doc_instBEqListItem_beq(v_00_u03b1_2986_, v_inst_2987_, v_x_2988_, v_x_2989_);
    crate::leanh::lean_dec_ref(v_x_2989_);
    crate::leanh::lean_dec_ref(v_x_2988_);
    v_r_2991_ = crate::leanh::lean_box((v_res_2990_) as usize);
    return v_r_2991_;
}
pub unsafe fn l_Lean_Doc_instBEqListItem___redArg(
    mut v_inst_2992_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2993_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2993_ = crate::leanh::lean_alloc_closure(
        l_Lean_Doc_instBEqListItem_beq___boxed as *mut core::ffi::c_void,
        4,
        2,
    );
    crate::leanh::lean_closure_set(v___x_2993_, 0, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_2993_, 1, v_inst_2992_);
    return v___x_2993_;
}
pub unsafe fn l_Lean_Doc_instBEqListItem(
    mut v_00_u03b1_2994_: *mut crate::leanh::LeanObject,
    mut v_inst_2995_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2996_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2996_ = crate::leanh::lean_alloc_closure(
        l_Lean_Doc_instBEqListItem_beq___boxed as *mut core::ffi::c_void,
        4,
        2,
    );
    crate::leanh::lean_closure_set(v___x_2996_, 0, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_2996_, 1, v_inst_2995_);
    return v___x_2996_;
}
pub unsafe fn l_Lean_Doc_instOrdListItem_ord___redArg(
    mut v_inst_2997_: *mut crate::leanh::LeanObject,
    mut v_x_2998_: *mut crate::leanh::LeanObject,
    mut v_x_2999_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_3000_: u8 = 0;
    v___x_3000_ = l_Array_compareLex___redArg(v_inst_2997_, v_x_2998_, v_x_2999_);
    if v___x_3000_ == 1 {
        return v___x_3000_;
    } else {
        return v___x_3000_;
    }
}
pub unsafe fn l_Lean_Doc_instOrdListItem_ord___redArg___boxed(
    mut v_inst_3001_: *mut crate::leanh::LeanObject,
    mut v_x_3002_: *mut crate::leanh::LeanObject,
    mut v_x_3003_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3004_: u8 = 0;
    let mut v_r_3005_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3004_ = l_Lean_Doc_instOrdListItem_ord___redArg(v_inst_3001_, v_x_3002_, v_x_3003_);
    crate::leanh::lean_dec_ref(v_x_3003_);
    crate::leanh::lean_dec_ref(v_x_3002_);
    v_r_3005_ = crate::leanh::lean_box((v_res_3004_) as usize);
    return v_r_3005_;
}
pub unsafe fn l_Lean_Doc_instOrdListItem_ord(
    mut v_00_u03b1_3006_: *mut crate::leanh::LeanObject,
    mut v_inst_3007_: *mut crate::leanh::LeanObject,
    mut v_x_3008_: *mut crate::leanh::LeanObject,
    mut v_x_3009_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_3010_: u8 = 0;
    v___x_3010_ = l_Lean_Doc_instOrdListItem_ord___redArg(v_inst_3007_, v_x_3008_, v_x_3009_);
    return v___x_3010_;
}
pub unsafe fn l_Lean_Doc_instOrdListItem_ord___boxed(
    mut v_00_u03b1_3011_: *mut crate::leanh::LeanObject,
    mut v_inst_3012_: *mut crate::leanh::LeanObject,
    mut v_x_3013_: *mut crate::leanh::LeanObject,
    mut v_x_3014_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3015_: u8 = 0;
    let mut v_r_3016_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3015_ =
        l_Lean_Doc_instOrdListItem_ord(v_00_u03b1_3011_, v_inst_3012_, v_x_3013_, v_x_3014_);
    crate::leanh::lean_dec_ref(v_x_3014_);
    crate::leanh::lean_dec_ref(v_x_3013_);
    v_r_3016_ = crate::leanh::lean_box((v_res_3015_) as usize);
    return v_r_3016_;
}
pub unsafe fn l_Lean_Doc_instOrdListItem___redArg(
    mut v_inst_3017_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3018_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3018_ = crate::leanh::lean_alloc_closure(
        l_Lean_Doc_instOrdListItem_ord___boxed as *mut core::ffi::c_void,
        4,
        2,
    );
    crate::leanh::lean_closure_set(v___x_3018_, 0, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_3018_, 1, v_inst_3017_);
    return v___x_3018_;
}
pub unsafe fn l_Lean_Doc_instOrdListItem(
    mut v_00_u03b1_3019_: *mut crate::leanh::LeanObject,
    mut v_inst_3020_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3021_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3021_ = crate::leanh::lean_alloc_closure(
        l_Lean_Doc_instOrdListItem_ord___boxed as *mut core::ffi::c_void,
        4,
        2,
    );
    crate::leanh::lean_closure_set(v___x_3021_, 0, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_3021_, 1, v_inst_3020_);
    return v___x_3021_;
}
pub unsafe fn l_Lean_Doc_instInhabitedListItem_default(
    mut v_00_u03b1_3024_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3025_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3025_ = l_Lean_Doc_instInhabitedListItem_default___closed__0;
    return v___x_3025_;
}
pub unsafe fn _init_l_Lean_Doc_instInhabitedListItem___closed__0() -> *mut crate::leanh::LeanObject
{
    let mut v___x_3026_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3026_ = l_Lean_Doc_instInhabitedListItem_default(crate::leanh::lean_box(0));
    return v___x_3026_;
}
pub unsafe fn l_Lean_Doc_instInhabitedListItem(
    mut v_a_3027_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3028_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3028_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Doc_instInhabitedListItem___closed__0),
        core::ptr::addr_of_mut!(l_Lean_Doc_instInhabitedListItem___closed__0_once),
        _init_l_Lean_Doc_instInhabitedListItem___closed__0,
    );
    return v___x_3028_;
}
pub unsafe fn _init_l_Lean_Doc_instReprDescItem_repr___redArg___closed__4()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3038_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3039_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3038_ = crate::leanh::lean_unsigned_to_nat(8);
    v___x_3039_ = lean_nat_to_int(v___x_3038_);
    return v___x_3039_;
}
pub unsafe fn l_Lean_Doc_instReprDescItem_repr___redArg(
    mut v_inst_3046_: *mut crate::leanh::LeanObject,
    mut v_inst_3047_: *mut crate::leanh::LeanObject,
    mut v_x_3048_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_term_3049_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_desc_3050_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3052_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3053_: u8 = 0;
    let mut v___x_3054_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3055_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3056_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3057_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3059_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3060_: u8 = 0;
    let mut v___x_3061_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3062_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3063_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3064_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3065_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3066_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3067_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3068_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3069_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3070_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3071_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3072_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3073_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3074_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3075_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3076_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3077_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3078_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3079_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3080_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3081_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3082_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_term_3049_ = crate::leanh::lean_ctor_get(v_x_3048_, 0);
                v_desc_3050_ = crate::leanh::lean_ctor_get(v_x_3048_, 1);
                v_isSharedCheck_3082_ = (!crate::leanh::lean_is_exclusive(v_x_3048_)) as u8;
                if v_isSharedCheck_3082_ == 0 {
                    v___x_3052_ = v_x_3048_;
                    v_isShared_3053_ = v_isSharedCheck_3082_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_desc_3050_);
                    crate::leanh::lean_inc(v_term_3049_);
                    crate::leanh::lean_dec(v_x_3048_);
                    v___x_3052_ = crate::leanh::lean_box(0);
                    v_isShared_3053_ = v_isSharedCheck_3082_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_3054_ = l_Lean_Doc_instReprListItem_repr___redArg___closed__5;
                v___x_3055_ = l_Lean_Doc_instReprDescItem_repr___redArg___closed__3;
                v___x_3056_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lean_Doc_instReprDescItem_repr___redArg___closed__4),
                    core::ptr::addr_of_mut!(
                        l_Lean_Doc_instReprDescItem_repr___redArg___closed__4_once
                    ),
                    _init_l_Lean_Doc_instReprDescItem_repr___redArg___closed__4,
                );
                v___x_3057_ = l_Array_repr___redArg(v_inst_3046_, v_term_3049_);
                if v_isShared_3053_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_3052_, 4);
                    crate::leanh::lean_ctor_set(v___x_3052_, 1, v___x_3057_);
                    crate::leanh::lean_ctor_set(v___x_3052_, 0, v___x_3056_);
                    v___x_3059_ = v___x_3052_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3081_ = crate::leanh::lean_alloc_ctor(4, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3081_, 0, v___x_3056_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3081_, 1, v___x_3057_);
                    v___x_3059_ = v_reuseFailAlloc_3081_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_3060_ = 0;
                v___x_3061_ = crate::leanh::lean_alloc_ctor(6, 1, (1) as u32);
                crate::leanh::lean_ctor_set(v___x_3061_, 0, v___x_3059_);
                crate::leanh::lean_ctor_set_uint8(
                    v___x_3061_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                    v___x_3060_,
                );
                v___x_3062_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3062_, 0, v___x_3055_);
                crate::leanh::lean_ctor_set(v___x_3062_, 1, v___x_3061_);
                v___x_3063_ = l_Lean_Doc_instReprDescItem_repr___redArg___closed__6;
                v___x_3064_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3064_, 0, v___x_3062_);
                crate::leanh::lean_ctor_set(v___x_3064_, 1, v___x_3063_);
                v___x_3065_ = crate::leanh::lean_box(1);
                v___x_3066_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3066_, 0, v___x_3064_);
                crate::leanh::lean_ctor_set(v___x_3066_, 1, v___x_3065_);
                v___x_3067_ = l_Lean_Doc_instReprDescItem_repr___redArg___closed__8;
                v___x_3068_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3068_, 0, v___x_3066_);
                crate::leanh::lean_ctor_set(v___x_3068_, 1, v___x_3067_);
                v___x_3069_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3069_, 0, v___x_3068_);
                crate::leanh::lean_ctor_set(v___x_3069_, 1, v___x_3054_);
                v___x_3070_ = l_Array_repr___redArg(v_inst_3047_, v_desc_3050_);
                v___x_3071_ = crate::leanh::lean_alloc_ctor(4, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3071_, 0, v___x_3056_);
                crate::leanh::lean_ctor_set(v___x_3071_, 1, v___x_3070_);
                v___x_3072_ = crate::leanh::lean_alloc_ctor(6, 1, (1) as u32);
                crate::leanh::lean_ctor_set(v___x_3072_, 0, v___x_3071_);
                crate::leanh::lean_ctor_set_uint8(
                    v___x_3072_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                    v___x_3060_,
                );
                v___x_3073_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3073_, 0, v___x_3069_);
                crate::leanh::lean_ctor_set(v___x_3073_, 1, v___x_3072_);
                v___x_3074_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lean_Doc_instReprListItem_repr___redArg___closed__10),
                    core::ptr::addr_of_mut!(
                        l_Lean_Doc_instReprListItem_repr___redArg___closed__10_once
                    ),
                    _init_l_Lean_Doc_instReprListItem_repr___redArg___closed__10,
                );
                v___x_3075_ = l_Lean_Doc_instReprListItem_repr___redArg___closed__11;
                v___x_3076_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3076_, 0, v___x_3075_);
                crate::leanh::lean_ctor_set(v___x_3076_, 1, v___x_3073_);
                v___x_3077_ = l_Lean_Doc_instReprListItem_repr___redArg___closed__12;
                v___x_3078_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3078_, 0, v___x_3076_);
                crate::leanh::lean_ctor_set(v___x_3078_, 1, v___x_3077_);
                v___x_3079_ = crate::leanh::lean_alloc_ctor(4, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3079_, 0, v___x_3074_);
                crate::leanh::lean_ctor_set(v___x_3079_, 1, v___x_3078_);
                v___x_3080_ = crate::leanh::lean_alloc_ctor(6, 1, (1) as u32);
                crate::leanh::lean_ctor_set(v___x_3080_, 0, v___x_3079_);
                crate::leanh::lean_ctor_set_uint8(
                    v___x_3080_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                    v___x_3060_,
                );
                return v___x_3080_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Doc_instReprDescItem_repr(
    mut v_00_u03b1_3083_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_3084_: *mut crate::leanh::LeanObject,
    mut v_inst_3085_: *mut crate::leanh::LeanObject,
    mut v_inst_3086_: *mut crate::leanh::LeanObject,
    mut v_x_3087_: *mut crate::leanh::LeanObject,
    mut v_prec_3088_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3089_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3089_ = l_Lean_Doc_instReprDescItem_repr___redArg(v_inst_3085_, v_inst_3086_, v_x_3087_);
    return v___x_3089_;
}
pub unsafe fn l_Lean_Doc_instReprDescItem_repr___boxed(
    mut v_00_u03b1_3090_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_3091_: *mut crate::leanh::LeanObject,
    mut v_inst_3092_: *mut crate::leanh::LeanObject,
    mut v_inst_3093_: *mut crate::leanh::LeanObject,
    mut v_x_3094_: *mut crate::leanh::LeanObject,
    mut v_prec_3095_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3096_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3096_ = l_Lean_Doc_instReprDescItem_repr(
        v_00_u03b1_3090_,
        v_00_u03b2_3091_,
        v_inst_3092_,
        v_inst_3093_,
        v_x_3094_,
        v_prec_3095_,
    );
    crate::leanh::lean_dec(v_prec_3095_);
    return v_res_3096_;
}
pub unsafe fn l_Lean_Doc_instReprDescItem___redArg(
    mut v_inst_3097_: *mut crate::leanh::LeanObject,
    mut v_inst_3098_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3099_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3099_ = crate::leanh::lean_alloc_closure(
        l_Lean_Doc_instReprDescItem_repr___boxed as *mut core::ffi::c_void,
        6,
        4,
    );
    crate::leanh::lean_closure_set(v___x_3099_, 0, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_3099_, 1, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_3099_, 2, v_inst_3097_);
    crate::leanh::lean_closure_set(v___x_3099_, 3, v_inst_3098_);
    return v___x_3099_;
}
pub unsafe fn l_Lean_Doc_instReprDescItem(
    mut v_00_u03b1_3100_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_3101_: *mut crate::leanh::LeanObject,
    mut v_inst_3102_: *mut crate::leanh::LeanObject,
    mut v_inst_3103_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3104_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3104_ = crate::leanh::lean_alloc_closure(
        l_Lean_Doc_instReprDescItem_repr___boxed as *mut core::ffi::c_void,
        6,
        4,
    );
    crate::leanh::lean_closure_set(v___x_3104_, 0, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_3104_, 1, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_3104_, 2, v_inst_3102_);
    crate::leanh::lean_closure_set(v___x_3104_, 3, v_inst_3103_);
    return v___x_3104_;
}
pub unsafe fn l_Lean_Doc_instBEqDescItem_beq___redArg(
    mut v_inst_3105_: *mut crate::leanh::LeanObject,
    mut v_inst_3106_: *mut crate::leanh::LeanObject,
    mut v_x_3107_: *mut crate::leanh::LeanObject,
    mut v_x_3108_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v_term_3109_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_desc_3110_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_term_3111_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_desc_3112_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3113_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3114_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3115_: u8 = 0;
    v_term_3109_ = crate::leanh::lean_ctor_get(v_x_3107_, 0);
    v_desc_3110_ = crate::leanh::lean_ctor_get(v_x_3107_, 1);
    v_term_3111_ = crate::leanh::lean_ctor_get(v_x_3108_, 0);
    v_desc_3112_ = crate::leanh::lean_ctor_get(v_x_3108_, 1);
    v___x_3113_ = lean_array_get_size(v_term_3109_);
    v___x_3114_ = lean_array_get_size(v_term_3111_);
    v___x_3115_ = lean_nat_dec_eq(v___x_3113_, v___x_3114_);
    if v___x_3115_ == 0 {
        crate::leanh::lean_dec_ref(v_inst_3106_);
        crate::leanh::lean_dec_ref(v_inst_3105_);
        return v___x_3115_;
    } else {
        let mut v___x_3116_: u8 = 0;
        v___x_3116_ =
            l_Array_isEqvAux___redArg(v_term_3109_, v_term_3111_, v_inst_3105_, v___x_3113_);
        if v___x_3116_ == 0 {
            crate::leanh::lean_dec_ref(v_inst_3106_);
            return v___x_3116_;
        } else {
            let mut v___x_3117_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_3118_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_3119_: u8 = 0;
            v___x_3117_ = lean_array_get_size(v_desc_3110_);
            v___x_3118_ = lean_array_get_size(v_desc_3112_);
            v___x_3119_ = lean_nat_dec_eq(v___x_3117_, v___x_3118_);
            if v___x_3119_ == 0 {
                crate::leanh::lean_dec_ref(v_inst_3106_);
                return v___x_3119_;
            } else {
                let mut v___x_3120_: u8 = 0;
                v___x_3120_ = l_Array_isEqvAux___redArg(
                    v_desc_3110_,
                    v_desc_3112_,
                    v_inst_3106_,
                    v___x_3117_,
                );
                return v___x_3120_;
            }
        }
    }
}
pub unsafe fn l_Lean_Doc_instBEqDescItem_beq___redArg___boxed(
    mut v_inst_3121_: *mut crate::leanh::LeanObject,
    mut v_inst_3122_: *mut crate::leanh::LeanObject,
    mut v_x_3123_: *mut crate::leanh::LeanObject,
    mut v_x_3124_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3125_: u8 = 0;
    let mut v_r_3126_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3125_ =
        l_Lean_Doc_instBEqDescItem_beq___redArg(v_inst_3121_, v_inst_3122_, v_x_3123_, v_x_3124_);
    crate::leanh::lean_dec_ref(v_x_3124_);
    crate::leanh::lean_dec_ref(v_x_3123_);
    v_r_3126_ = crate::leanh::lean_box((v_res_3125_) as usize);
    return v_r_3126_;
}
pub unsafe fn l_Lean_Doc_instBEqDescItem_beq(
    mut v_00_u03b1_3127_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_3128_: *mut crate::leanh::LeanObject,
    mut v_inst_3129_: *mut crate::leanh::LeanObject,
    mut v_inst_3130_: *mut crate::leanh::LeanObject,
    mut v_x_3131_: *mut crate::leanh::LeanObject,
    mut v_x_3132_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_3133_: u8 = 0;
    v___x_3133_ =
        l_Lean_Doc_instBEqDescItem_beq___redArg(v_inst_3129_, v_inst_3130_, v_x_3131_, v_x_3132_);
    return v___x_3133_;
}
pub unsafe fn l_Lean_Doc_instBEqDescItem_beq___boxed(
    mut v_00_u03b1_3134_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_3135_: *mut crate::leanh::LeanObject,
    mut v_inst_3136_: *mut crate::leanh::LeanObject,
    mut v_inst_3137_: *mut crate::leanh::LeanObject,
    mut v_x_3138_: *mut crate::leanh::LeanObject,
    mut v_x_3139_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3140_: u8 = 0;
    let mut v_r_3141_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3140_ = l_Lean_Doc_instBEqDescItem_beq(
        v_00_u03b1_3134_,
        v_00_u03b2_3135_,
        v_inst_3136_,
        v_inst_3137_,
        v_x_3138_,
        v_x_3139_,
    );
    crate::leanh::lean_dec_ref(v_x_3139_);
    crate::leanh::lean_dec_ref(v_x_3138_);
    v_r_3141_ = crate::leanh::lean_box((v_res_3140_) as usize);
    return v_r_3141_;
}
pub unsafe fn l_Lean_Doc_instBEqDescItem___redArg(
    mut v_inst_3142_: *mut crate::leanh::LeanObject,
    mut v_inst_3143_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3144_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3144_ = crate::leanh::lean_alloc_closure(
        l_Lean_Doc_instBEqDescItem_beq___boxed as *mut core::ffi::c_void,
        6,
        4,
    );
    crate::leanh::lean_closure_set(v___x_3144_, 0, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_3144_, 1, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_3144_, 2, v_inst_3142_);
    crate::leanh::lean_closure_set(v___x_3144_, 3, v_inst_3143_);
    return v___x_3144_;
}
pub unsafe fn l_Lean_Doc_instBEqDescItem(
    mut v_00_u03b1_3145_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_3146_: *mut crate::leanh::LeanObject,
    mut v_inst_3147_: *mut crate::leanh::LeanObject,
    mut v_inst_3148_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3149_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3149_ = crate::leanh::lean_alloc_closure(
        l_Lean_Doc_instBEqDescItem_beq___boxed as *mut core::ffi::c_void,
        6,
        4,
    );
    crate::leanh::lean_closure_set(v___x_3149_, 0, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_3149_, 1, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_3149_, 2, v_inst_3147_);
    crate::leanh::lean_closure_set(v___x_3149_, 3, v_inst_3148_);
    return v___x_3149_;
}
pub unsafe fn l_Lean_Doc_instOrdDescItem_ord___redArg(
    mut v_inst_3150_: *mut crate::leanh::LeanObject,
    mut v_inst_3151_: *mut crate::leanh::LeanObject,
    mut v_x_3152_: *mut crate::leanh::LeanObject,
    mut v_x_3153_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v_term_3154_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_desc_3155_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_term_3156_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_desc_3157_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3158_: u8 = 0;
    v_term_3154_ = crate::leanh::lean_ctor_get(v_x_3152_, 0);
    v_desc_3155_ = crate::leanh::lean_ctor_get(v_x_3152_, 1);
    v_term_3156_ = crate::leanh::lean_ctor_get(v_x_3153_, 0);
    v_desc_3157_ = crate::leanh::lean_ctor_get(v_x_3153_, 1);
    v___x_3158_ = l_Array_compareLex___redArg(v_inst_3150_, v_term_3154_, v_term_3156_);
    if v___x_3158_ == 1 {
        let mut v___x_3159_: u8 = 0;
        v___x_3159_ = l_Array_compareLex___redArg(v_inst_3151_, v_desc_3155_, v_desc_3157_);
        if v___x_3159_ == 1 {
            return v___x_3159_;
        } else {
            return v___x_3159_;
        }
    } else {
        crate::leanh::lean_dec_ref(v_inst_3151_);
        return v___x_3158_;
    }
}
pub unsafe fn l_Lean_Doc_instOrdDescItem_ord___redArg___boxed(
    mut v_inst_3160_: *mut crate::leanh::LeanObject,
    mut v_inst_3161_: *mut crate::leanh::LeanObject,
    mut v_x_3162_: *mut crate::leanh::LeanObject,
    mut v_x_3163_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3164_: u8 = 0;
    let mut v_r_3165_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3164_ =
        l_Lean_Doc_instOrdDescItem_ord___redArg(v_inst_3160_, v_inst_3161_, v_x_3162_, v_x_3163_);
    crate::leanh::lean_dec_ref(v_x_3163_);
    crate::leanh::lean_dec_ref(v_x_3162_);
    v_r_3165_ = crate::leanh::lean_box((v_res_3164_) as usize);
    return v_r_3165_;
}
pub unsafe fn l_Lean_Doc_instOrdDescItem_ord(
    mut v_00_u03b1_3166_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_3167_: *mut crate::leanh::LeanObject,
    mut v_inst_3168_: *mut crate::leanh::LeanObject,
    mut v_inst_3169_: *mut crate::leanh::LeanObject,
    mut v_x_3170_: *mut crate::leanh::LeanObject,
    mut v_x_3171_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_3172_: u8 = 0;
    v___x_3172_ =
        l_Lean_Doc_instOrdDescItem_ord___redArg(v_inst_3168_, v_inst_3169_, v_x_3170_, v_x_3171_);
    return v___x_3172_;
}
pub unsafe fn l_Lean_Doc_instOrdDescItem_ord___boxed(
    mut v_00_u03b1_3173_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_3174_: *mut crate::leanh::LeanObject,
    mut v_inst_3175_: *mut crate::leanh::LeanObject,
    mut v_inst_3176_: *mut crate::leanh::LeanObject,
    mut v_x_3177_: *mut crate::leanh::LeanObject,
    mut v_x_3178_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3179_: u8 = 0;
    let mut v_r_3180_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3179_ = l_Lean_Doc_instOrdDescItem_ord(
        v_00_u03b1_3173_,
        v_00_u03b2_3174_,
        v_inst_3175_,
        v_inst_3176_,
        v_x_3177_,
        v_x_3178_,
    );
    crate::leanh::lean_dec_ref(v_x_3178_);
    crate::leanh::lean_dec_ref(v_x_3177_);
    v_r_3180_ = crate::leanh::lean_box((v_res_3179_) as usize);
    return v_r_3180_;
}
pub unsafe fn l_Lean_Doc_instOrdDescItem___redArg(
    mut v_inst_3181_: *mut crate::leanh::LeanObject,
    mut v_inst_3182_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3183_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3183_ = crate::leanh::lean_alloc_closure(
        l_Lean_Doc_instOrdDescItem_ord___boxed as *mut core::ffi::c_void,
        6,
        4,
    );
    crate::leanh::lean_closure_set(v___x_3183_, 0, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_3183_, 1, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_3183_, 2, v_inst_3181_);
    crate::leanh::lean_closure_set(v___x_3183_, 3, v_inst_3182_);
    return v___x_3183_;
}
pub unsafe fn l_Lean_Doc_instOrdDescItem(
    mut v_00_u03b1_3184_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_3185_: *mut crate::leanh::LeanObject,
    mut v_inst_3186_: *mut crate::leanh::LeanObject,
    mut v_inst_3187_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3188_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3188_ = crate::leanh::lean_alloc_closure(
        l_Lean_Doc_instOrdDescItem_ord___boxed as *mut core::ffi::c_void,
        6,
        4,
    );
    crate::leanh::lean_closure_set(v___x_3188_, 0, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_3188_, 1, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_3188_, 2, v_inst_3186_);
    crate::leanh::lean_closure_set(v___x_3188_, 3, v_inst_3187_);
    return v___x_3188_;
}
pub unsafe fn l_Lean_Doc_instInhabitedDescItem_default(
    mut v_00_u03b1_3191_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_3192_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3193_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3193_ = l_Lean_Doc_instInhabitedDescItem_default___closed__0;
    return v___x_3193_;
}
pub unsafe fn _init_l_Lean_Doc_instInhabitedDescItem___closed__0() -> *mut crate::leanh::LeanObject
{
    let mut v___x_3194_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3194_ = l_Lean_Doc_instInhabitedDescItem_default(
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
    );
    return v___x_3194_;
}
pub unsafe fn l_Lean_Doc_instInhabitedDescItem(
    mut v_a_3195_: *mut crate::leanh::LeanObject,
    mut v_a_3196_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3197_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3197_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Doc_instInhabitedDescItem___closed__0),
        core::ptr::addr_of_mut!(l_Lean_Doc_instInhabitedDescItem___closed__0_once),
        _init_l_Lean_Doc_instInhabitedDescItem___closed__0,
    );
    return v___x_3197_;
}
pub unsafe fn l_Lean_Doc_Block_ctorIdx___redArg(
    mut v_x_3198_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    match crate::leanh::lean_obj_tag(v_x_3198_) {
        0 => {
            let mut v___x_3199_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_3199_ = crate::leanh::lean_unsigned_to_nat(0);
            return v___x_3199_;
        }
        1 => {
            let mut v___x_3200_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_3200_ = crate::leanh::lean_unsigned_to_nat(1);
            return v___x_3200_;
        }
        2 => {
            let mut v___x_3201_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_3201_ = crate::leanh::lean_unsigned_to_nat(2);
            return v___x_3201_;
        }
        3 => {
            let mut v___x_3202_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_3202_ = crate::leanh::lean_unsigned_to_nat(3);
            return v___x_3202_;
        }
        4 => {
            let mut v___x_3203_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_3203_ = crate::leanh::lean_unsigned_to_nat(4);
            return v___x_3203_;
        }
        5 => {
            let mut v___x_3204_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_3204_ = crate::leanh::lean_unsigned_to_nat(5);
            return v___x_3204_;
        }
        6 => {
            let mut v___x_3205_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_3205_ = crate::leanh::lean_unsigned_to_nat(6);
            return v___x_3205_;
        }
        _ => {
            let mut v___x_3206_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_3206_ = crate::leanh::lean_unsigned_to_nat(7);
            return v___x_3206_;
        }
    }
}
pub unsafe fn l_Lean_Doc_Block_ctorIdx___redArg___boxed(
    mut v_x_3207_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3208_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3208_ = l_Lean_Doc_Block_ctorIdx___redArg(v_x_3207_);
    crate::leanh::lean_dec_ref(v_x_3207_);
    return v_res_3208_;
}
pub unsafe fn l_Lean_Doc_Block_ctorIdx(
    mut v_i_3209_: *mut crate::leanh::LeanObject,
    mut v_b_3210_: *mut crate::leanh::LeanObject,
    mut v_x_3211_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3212_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3212_ = l_Lean_Doc_Block_ctorIdx___redArg(v_x_3211_);
    return v___x_3212_;
}
pub unsafe fn l_Lean_Doc_Block_ctorIdx___boxed(
    mut v_i_3213_: *mut crate::leanh::LeanObject,
    mut v_b_3214_: *mut crate::leanh::LeanObject,
    mut v_x_3215_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3216_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3216_ = l_Lean_Doc_Block_ctorIdx(v_i_3213_, v_b_3214_, v_x_3215_);
    crate::leanh::lean_dec_ref(v_x_3215_);
    return v_res_3216_;
}
pub unsafe fn l_Lean_Doc_Block_ctorElim___redArg(
    mut v_t_3217_: *mut crate::leanh::LeanObject,
    mut v_k_3218_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    match crate::leanh::lean_obj_tag(v_t_3217_) {
        3 => {
            let mut v_start_3219_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_items_3220_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_3221_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v_start_3219_ = crate::leanh::lean_ctor_get(v_t_3217_, 0);
            crate::leanh::lean_inc(v_start_3219_);
            v_items_3220_ = crate::leanh::lean_ctor_get(v_t_3217_, 1);
            crate::leanh::lean_inc_ref(v_items_3220_);
            crate::leanh::lean_dec_ref_known(v_t_3217_, 2);
            v___x_3221_ = crate::leanh::lean_apply_2(v_k_3218_, v_start_3219_, v_items_3220_);
            return v___x_3221_;
        }
        7 => {
            let mut v_container_3222_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_content_3223_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_3224_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v_container_3222_ = crate::leanh::lean_ctor_get(v_t_3217_, 0);
            crate::leanh::lean_inc(v_container_3222_);
            v_content_3223_ = crate::leanh::lean_ctor_get(v_t_3217_, 1);
            crate::leanh::lean_inc_ref(v_content_3223_);
            crate::leanh::lean_dec_ref_known(v_t_3217_, 2);
            v___x_3224_ = crate::leanh::lean_apply_2(v_k_3218_, v_container_3222_, v_content_3223_);
            return v___x_3224_;
        }
        _ => {
            let mut v_contents_3225_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_3226_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v_contents_3225_ = crate::leanh::lean_ctor_get(v_t_3217_, 0);
            crate::leanh::lean_inc_ref(v_contents_3225_);
            crate::leanh::lean_dec_ref(v_t_3217_);
            v___x_3226_ = crate::leanh::lean_apply_1(v_k_3218_, v_contents_3225_);
            return v___x_3226_;
        }
    }
}
pub unsafe fn l_Lean_Doc_Block_ctorElim(
    mut v_i_3227_: *mut crate::leanh::LeanObject,
    mut v_b_3228_: *mut crate::leanh::LeanObject,
    mut v_motive__1_3229_: *mut crate::leanh::LeanObject,
    mut v_ctorIdx_3230_: *mut crate::leanh::LeanObject,
    mut v_t_3231_: *mut crate::leanh::LeanObject,
    mut v_h_3232_: *mut crate::leanh::LeanObject,
    mut v_k_3233_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3234_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3234_ = l_Lean_Doc_Block_ctorElim___redArg(v_t_3231_, v_k_3233_);
    return v___x_3234_;
}
pub unsafe fn l_Lean_Doc_Block_ctorElim___boxed(
    mut v_i_3235_: *mut crate::leanh::LeanObject,
    mut v_b_3236_: *mut crate::leanh::LeanObject,
    mut v_motive__1_3237_: *mut crate::leanh::LeanObject,
    mut v_ctorIdx_3238_: *mut crate::leanh::LeanObject,
    mut v_t_3239_: *mut crate::leanh::LeanObject,
    mut v_h_3240_: *mut crate::leanh::LeanObject,
    mut v_k_3241_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3242_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3242_ = l_Lean_Doc_Block_ctorElim(
        v_i_3235_,
        v_b_3236_,
        v_motive__1_3237_,
        v_ctorIdx_3238_,
        v_t_3239_,
        v_h_3240_,
        v_k_3241_,
    );
    crate::leanh::lean_dec(v_ctorIdx_3238_);
    return v_res_3242_;
}
pub unsafe fn l_Lean_Doc_Block_para_elim___redArg(
    mut v_t_3243_: *mut crate::leanh::LeanObject,
    mut v_para_3244_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3245_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3245_ = l_Lean_Doc_Block_ctorElim___redArg(v_t_3243_, v_para_3244_);
    return v___x_3245_;
}
pub unsafe fn l_Lean_Doc_Block_para_elim(
    mut v_i_3246_: *mut crate::leanh::LeanObject,
    mut v_b_3247_: *mut crate::leanh::LeanObject,
    mut v_motive__1_3248_: *mut crate::leanh::LeanObject,
    mut v_t_3249_: *mut crate::leanh::LeanObject,
    mut v_h_3250_: *mut crate::leanh::LeanObject,
    mut v_para_3251_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3252_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3252_ = l_Lean_Doc_Block_ctorElim___redArg(v_t_3249_, v_para_3251_);
    return v___x_3252_;
}
pub unsafe fn l_Lean_Doc_Block_code_elim___redArg(
    mut v_t_3253_: *mut crate::leanh::LeanObject,
    mut v_code_3254_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3255_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3255_ = l_Lean_Doc_Block_ctorElim___redArg(v_t_3253_, v_code_3254_);
    return v___x_3255_;
}
pub unsafe fn l_Lean_Doc_Block_code_elim(
    mut v_i_3256_: *mut crate::leanh::LeanObject,
    mut v_b_3257_: *mut crate::leanh::LeanObject,
    mut v_motive__1_3258_: *mut crate::leanh::LeanObject,
    mut v_t_3259_: *mut crate::leanh::LeanObject,
    mut v_h_3260_: *mut crate::leanh::LeanObject,
    mut v_code_3261_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3262_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3262_ = l_Lean_Doc_Block_ctorElim___redArg(v_t_3259_, v_code_3261_);
    return v___x_3262_;
}
pub unsafe fn l_Lean_Doc_Block_ul_elim___redArg(
    mut v_t_3263_: *mut crate::leanh::LeanObject,
    mut v_ul_3264_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3265_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3265_ = l_Lean_Doc_Block_ctorElim___redArg(v_t_3263_, v_ul_3264_);
    return v___x_3265_;
}
pub unsafe fn l_Lean_Doc_Block_ul_elim(
    mut v_i_3266_: *mut crate::leanh::LeanObject,
    mut v_b_3267_: *mut crate::leanh::LeanObject,
    mut v_motive__1_3268_: *mut crate::leanh::LeanObject,
    mut v_t_3269_: *mut crate::leanh::LeanObject,
    mut v_h_3270_: *mut crate::leanh::LeanObject,
    mut v_ul_3271_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3272_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3272_ = l_Lean_Doc_Block_ctorElim___redArg(v_t_3269_, v_ul_3271_);
    return v___x_3272_;
}
pub unsafe fn l_Lean_Doc_Block_ol_elim___redArg(
    mut v_t_3273_: *mut crate::leanh::LeanObject,
    mut v_ol_3274_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3275_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3275_ = l_Lean_Doc_Block_ctorElim___redArg(v_t_3273_, v_ol_3274_);
    return v___x_3275_;
}
pub unsafe fn l_Lean_Doc_Block_ol_elim(
    mut v_i_3276_: *mut crate::leanh::LeanObject,
    mut v_b_3277_: *mut crate::leanh::LeanObject,
    mut v_motive__1_3278_: *mut crate::leanh::LeanObject,
    mut v_t_3279_: *mut crate::leanh::LeanObject,
    mut v_h_3280_: *mut crate::leanh::LeanObject,
    mut v_ol_3281_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3282_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3282_ = l_Lean_Doc_Block_ctorElim___redArg(v_t_3279_, v_ol_3281_);
    return v___x_3282_;
}
pub unsafe fn l_Lean_Doc_Block_dl_elim___redArg(
    mut v_t_3283_: *mut crate::leanh::LeanObject,
    mut v_dl_3284_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3285_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3285_ = l_Lean_Doc_Block_ctorElim___redArg(v_t_3283_, v_dl_3284_);
    return v___x_3285_;
}
pub unsafe fn l_Lean_Doc_Block_dl_elim(
    mut v_i_3286_: *mut crate::leanh::LeanObject,
    mut v_b_3287_: *mut crate::leanh::LeanObject,
    mut v_motive__1_3288_: *mut crate::leanh::LeanObject,
    mut v_t_3289_: *mut crate::leanh::LeanObject,
    mut v_h_3290_: *mut crate::leanh::LeanObject,
    mut v_dl_3291_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3292_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3292_ = l_Lean_Doc_Block_ctorElim___redArg(v_t_3289_, v_dl_3291_);
    return v___x_3292_;
}
pub unsafe fn l_Lean_Doc_Block_blockquote_elim___redArg(
    mut v_t_3293_: *mut crate::leanh::LeanObject,
    mut v_blockquote_3294_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3295_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3295_ = l_Lean_Doc_Block_ctorElim___redArg(v_t_3293_, v_blockquote_3294_);
    return v___x_3295_;
}
pub unsafe fn l_Lean_Doc_Block_blockquote_elim(
    mut v_i_3296_: *mut crate::leanh::LeanObject,
    mut v_b_3297_: *mut crate::leanh::LeanObject,
    mut v_motive__1_3298_: *mut crate::leanh::LeanObject,
    mut v_t_3299_: *mut crate::leanh::LeanObject,
    mut v_h_3300_: *mut crate::leanh::LeanObject,
    mut v_blockquote_3301_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3302_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3302_ = l_Lean_Doc_Block_ctorElim___redArg(v_t_3299_, v_blockquote_3301_);
    return v___x_3302_;
}
pub unsafe fn l_Lean_Doc_Block_concat_elim___redArg(
    mut v_t_3303_: *mut crate::leanh::LeanObject,
    mut v_concat_3304_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3305_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3305_ = l_Lean_Doc_Block_ctorElim___redArg(v_t_3303_, v_concat_3304_);
    return v___x_3305_;
}
pub unsafe fn l_Lean_Doc_Block_concat_elim(
    mut v_i_3306_: *mut crate::leanh::LeanObject,
    mut v_b_3307_: *mut crate::leanh::LeanObject,
    mut v_motive__1_3308_: *mut crate::leanh::LeanObject,
    mut v_t_3309_: *mut crate::leanh::LeanObject,
    mut v_h_3310_: *mut crate::leanh::LeanObject,
    mut v_concat_3311_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3312_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3312_ = l_Lean_Doc_Block_ctorElim___redArg(v_t_3309_, v_concat_3311_);
    return v___x_3312_;
}
pub unsafe fn l_Lean_Doc_Block_other_elim___redArg(
    mut v_t_3313_: *mut crate::leanh::LeanObject,
    mut v_other_3314_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3315_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3315_ = l_Lean_Doc_Block_ctorElim___redArg(v_t_3313_, v_other_3314_);
    return v___x_3315_;
}
pub unsafe fn l_Lean_Doc_Block_other_elim(
    mut v_i_3316_: *mut crate::leanh::LeanObject,
    mut v_b_3317_: *mut crate::leanh::LeanObject,
    mut v_motive__1_3318_: *mut crate::leanh::LeanObject,
    mut v_t_3319_: *mut crate::leanh::LeanObject,
    mut v_h_3320_: *mut crate::leanh::LeanObject,
    mut v_other_3321_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3322_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3322_ = l_Lean_Doc_Block_ctorElim___redArg(v_t_3319_, v_other_3321_);
    return v___x_3322_;
}
pub unsafe fn l_Lean_Doc_instBEqBlock_beq___redArg___boxed(
    mut v_inst_3323_: *mut crate::leanh::LeanObject,
    mut v_inst_3324_: *mut crate::leanh::LeanObject,
    mut v_x_3325_: *mut crate::leanh::LeanObject,
    mut v_x_3326_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3327_: u8 = 0;
    let mut v_r_3328_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3327_ =
        l_Lean_Doc_instBEqBlock_beq___redArg(v_inst_3323_, v_inst_3324_, v_x_3325_, v_x_3326_);
    v_r_3328_ = crate::leanh::lean_box((v_res_3327_) as usize);
    return v_r_3328_;
}
pub unsafe fn l_Lean_Doc_instBEqBlock_beq___redArg(
    mut v_inst_3329_: *mut crate::leanh::LeanObject,
    mut v_inst_3330_: *mut crate::leanh::LeanObject,
    mut v_x_3331_: *mut crate::leanh::LeanObject,
    mut v_x_3332_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v_localinst_3333_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3335_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_b_3336_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3337_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3338_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3339_: u8 = 0;
    let mut v___x_3340_: u8 = 0;
    let mut v_contents_3341_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_contents_3342_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3343_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3344_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3345_: u8 = 0;
    let mut v___x_3346_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3347_: u8 = 0;
    let mut v___x_3348_: u8 = 0;
    let mut v_content_3349_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_content_3350_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3351_: u8 = 0;
    let mut v___x_3352_: u8 = 0;
    let mut v_items_3353_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_items_3354_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3355_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3356_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3357_: u8 = 0;
    let mut v___x_3358_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3359_: u8 = 0;
    let mut v___x_3360_: u8 = 0;
    let mut v_start_3361_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_items_3362_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_start_3363_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_items_3364_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3365_: u8 = 0;
    let mut v___x_3366_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3367_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3368_: u8 = 0;
    let mut v___x_3369_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3370_: u8 = 0;
    let mut v___x_3371_: u8 = 0;
    let mut v_items_3372_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_items_3373_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3374_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3375_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3376_: u8 = 0;
    let mut v___x_3377_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3378_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3379_: u8 = 0;
    let mut v___x_3380_: u8 = 0;
    let mut v_items_3381_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_items_3382_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3383_: u8 = 0;
    let mut v_content_3384_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_content_3385_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3386_: u8 = 0;
    let mut v_container_3387_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_content_3388_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_container_3389_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_content_3390_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3391_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3392_: u8 = 0;
    let mut v___x_3393_: u8 = 0;
    let mut v___x_3394_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3395_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3396_: u8 = 0;
    let mut v___x_3397_: u8 = 0;
    let mut v___x_3398_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                crate::leanh::lean_inc_ref(v_inst_3330_);
                crate::leanh::lean_inc_ref(v_inst_3329_);
                v_localinst_3333_ = crate::leanh::lean_alloc_closure(
                    l_Lean_Doc_instBEqBlock_beq___redArg___boxed as *mut core::ffi::c_void,
                    4,
                    2,
                );
                crate::leanh::lean_closure_set(v_localinst_3333_, 0, v_inst_3329_);
                crate::leanh::lean_closure_set(v_localinst_3333_, 1, v_inst_3330_);
                match crate::leanh::lean_obj_tag(v_x_3331_) {
                    0 => {
                        crate::leanh::lean_dec_ref(v_localinst_3333_);
                        crate::leanh::lean_dec_ref(v_inst_3330_);
                        if crate::leanh::lean_obj_tag(v_x_3332_) == 0 {
                            v_contents_3341_ = crate::leanh::lean_ctor_get(v_x_3331_, 0);
                            crate::leanh::lean_inc_ref(v_contents_3341_);
                            crate::leanh::lean_dec_ref_known(v_x_3331_, 1);
                            v_contents_3342_ = crate::leanh::lean_ctor_get(v_x_3332_, 0);
                            crate::leanh::lean_inc_ref(v_contents_3342_);
                            crate::leanh::lean_dec_ref_known(v_x_3332_, 1);
                            v___x_3343_ = lean_array_get_size(v_contents_3341_);
                            v___x_3344_ = lean_array_get_size(v_contents_3342_);
                            v___x_3345_ = lean_nat_dec_eq(v___x_3343_, v___x_3344_);
                            if v___x_3345_ == 0 {
                                crate::leanh::lean_dec_ref(v_contents_3342_);
                                crate::leanh::lean_dec_ref(v_contents_3341_);
                                crate::leanh::lean_dec_ref(v_inst_3329_);
                                return v___x_3345_;
                            } else {
                                v___x_3346_ = crate::leanh::lean_alloc_closure(
                                    l_Lean_Doc_instBEqInline_beq___boxed as *mut core::ffi::c_void,
                                    4,
                                    2,
                                );
                                crate::leanh::lean_closure_set(
                                    v___x_3346_,
                                    0,
                                    crate::leanh::lean_box(0),
                                );
                                crate::leanh::lean_closure_set(v___x_3346_, 1, v_inst_3329_);
                                v___x_3347_ = l_Array_isEqvAux___redArg(
                                    v_contents_3341_,
                                    v_contents_3342_,
                                    v___x_3346_,
                                    v___x_3343_,
                                );
                                crate::leanh::lean_dec_ref(v_contents_3342_);
                                crate::leanh::lean_dec_ref(v_contents_3341_);
                                return v___x_3347_;
                            }
                        } else {
                            crate::leanh::lean_dec_ref_known(v_x_3331_, 1);
                            crate::leanh::lean_dec_ref(v_x_3332_);
                            crate::leanh::lean_dec_ref(v_inst_3329_);
                            v___x_3348_ = 0;
                            return v___x_3348_;
                        }
                    }
                    1 => {
                        crate::leanh::lean_dec_ref(v_localinst_3333_);
                        crate::leanh::lean_dec_ref(v_inst_3330_);
                        crate::leanh::lean_dec_ref(v_inst_3329_);
                        if crate::leanh::lean_obj_tag(v_x_3332_) == 1 {
                            v_content_3349_ = crate::leanh::lean_ctor_get(v_x_3331_, 0);
                            crate::leanh::lean_inc_ref(v_content_3349_);
                            crate::leanh::lean_dec_ref_known(v_x_3331_, 1);
                            v_content_3350_ = crate::leanh::lean_ctor_get(v_x_3332_, 0);
                            crate::leanh::lean_inc_ref(v_content_3350_);
                            crate::leanh::lean_dec_ref_known(v_x_3332_, 1);
                            v___x_3351_ = lean_string_dec_eq(v_content_3349_, v_content_3350_);
                            crate::leanh::lean_dec_ref(v_content_3350_);
                            crate::leanh::lean_dec_ref(v_content_3349_);
                            return v___x_3351_;
                        } else {
                            crate::leanh::lean_dec_ref_known(v_x_3331_, 1);
                            crate::leanh::lean_dec_ref(v_x_3332_);
                            v___x_3352_ = 0;
                            return v___x_3352_;
                        }
                    }
                    2 => {
                        crate::leanh::lean_dec_ref(v_inst_3330_);
                        crate::leanh::lean_dec_ref(v_inst_3329_);
                        if crate::leanh::lean_obj_tag(v_x_3332_) == 2 {
                            v_items_3353_ = crate::leanh::lean_ctor_get(v_x_3331_, 0);
                            crate::leanh::lean_inc_ref(v_items_3353_);
                            crate::leanh::lean_dec_ref_known(v_x_3331_, 1);
                            v_items_3354_ = crate::leanh::lean_ctor_get(v_x_3332_, 0);
                            crate::leanh::lean_inc_ref(v_items_3354_);
                            crate::leanh::lean_dec_ref_known(v_x_3332_, 1);
                            v___x_3355_ = lean_array_get_size(v_items_3353_);
                            v___x_3356_ = lean_array_get_size(v_items_3354_);
                            v___x_3357_ = lean_nat_dec_eq(v___x_3355_, v___x_3356_);
                            if v___x_3357_ == 0 {
                                crate::leanh::lean_dec_ref(v_items_3354_);
                                crate::leanh::lean_dec_ref(v_items_3353_);
                                crate::leanh::lean_dec_ref(v_localinst_3333_);
                                return v___x_3357_;
                            } else {
                                v___x_3358_ = crate::leanh::lean_alloc_closure(
                                    l_Lean_Doc_instBEqListItem_beq___boxed
                                        as *mut core::ffi::c_void,
                                    4,
                                    2,
                                );
                                crate::leanh::lean_closure_set(
                                    v___x_3358_,
                                    0,
                                    crate::leanh::lean_box(0),
                                );
                                crate::leanh::lean_closure_set(v___x_3358_, 1, v_localinst_3333_);
                                v___x_3359_ = l_Array_isEqvAux___redArg(
                                    v_items_3353_,
                                    v_items_3354_,
                                    v___x_3358_,
                                    v___x_3355_,
                                );
                                crate::leanh::lean_dec_ref(v_items_3354_);
                                crate::leanh::lean_dec_ref(v_items_3353_);
                                return v___x_3359_;
                            }
                        } else {
                            crate::leanh::lean_dec_ref_known(v_x_3331_, 1);
                            crate::leanh::lean_dec_ref(v_localinst_3333_);
                            crate::leanh::lean_dec_ref(v_x_3332_);
                            v___x_3360_ = 0;
                            return v___x_3360_;
                        }
                    }
                    3 => {
                        crate::leanh::lean_dec_ref(v_inst_3330_);
                        crate::leanh::lean_dec_ref(v_inst_3329_);
                        if crate::leanh::lean_obj_tag(v_x_3332_) == 3 {
                            v_start_3361_ = crate::leanh::lean_ctor_get(v_x_3331_, 0);
                            crate::leanh::lean_inc(v_start_3361_);
                            v_items_3362_ = crate::leanh::lean_ctor_get(v_x_3331_, 1);
                            crate::leanh::lean_inc_ref(v_items_3362_);
                            crate::leanh::lean_dec_ref_known(v_x_3331_, 2);
                            v_start_3363_ = crate::leanh::lean_ctor_get(v_x_3332_, 0);
                            crate::leanh::lean_inc(v_start_3363_);
                            v_items_3364_ = crate::leanh::lean_ctor_get(v_x_3332_, 1);
                            crate::leanh::lean_inc_ref(v_items_3364_);
                            crate::leanh::lean_dec_ref_known(v_x_3332_, 2);
                            v___x_3365_ = lean_int_dec_eq(v_start_3361_, v_start_3363_);
                            crate::leanh::lean_dec(v_start_3363_);
                            crate::leanh::lean_dec(v_start_3361_);
                            if v___x_3365_ == 0 {
                                crate::leanh::lean_dec_ref(v_items_3364_);
                                crate::leanh::lean_dec_ref(v_items_3362_);
                                crate::leanh::lean_dec_ref(v_localinst_3333_);
                                return v___x_3365_;
                            } else {
                                v___x_3366_ = lean_array_get_size(v_items_3362_);
                                v___x_3367_ = lean_array_get_size(v_items_3364_);
                                v___x_3368_ = lean_nat_dec_eq(v___x_3366_, v___x_3367_);
                                if v___x_3368_ == 0 {
                                    crate::leanh::lean_dec_ref(v_items_3364_);
                                    crate::leanh::lean_dec_ref(v_items_3362_);
                                    crate::leanh::lean_dec_ref(v_localinst_3333_);
                                    return v___x_3368_;
                                } else {
                                    v___x_3369_ = crate::leanh::lean_alloc_closure(
                                        l_Lean_Doc_instBEqListItem_beq___boxed
                                            as *mut core::ffi::c_void,
                                        4,
                                        2,
                                    );
                                    crate::leanh::lean_closure_set(
                                        v___x_3369_,
                                        0,
                                        crate::leanh::lean_box(0),
                                    );
                                    crate::leanh::lean_closure_set(
                                        v___x_3369_,
                                        1,
                                        v_localinst_3333_,
                                    );
                                    v___x_3370_ = l_Array_isEqvAux___redArg(
                                        v_items_3362_,
                                        v_items_3364_,
                                        v___x_3369_,
                                        v___x_3366_,
                                    );
                                    crate::leanh::lean_dec_ref(v_items_3364_);
                                    crate::leanh::lean_dec_ref(v_items_3362_);
                                    return v___x_3370_;
                                }
                            }
                        } else {
                            crate::leanh::lean_dec_ref_known(v_x_3331_, 2);
                            crate::leanh::lean_dec_ref(v_localinst_3333_);
                            crate::leanh::lean_dec_ref(v_x_3332_);
                            v___x_3371_ = 0;
                            return v___x_3371_;
                        }
                    }
                    4 => {
                        crate::leanh::lean_dec_ref(v_inst_3330_);
                        if crate::leanh::lean_obj_tag(v_x_3332_) == 4 {
                            v_items_3372_ = crate::leanh::lean_ctor_get(v_x_3331_, 0);
                            crate::leanh::lean_inc_ref(v_items_3372_);
                            crate::leanh::lean_dec_ref_known(v_x_3331_, 1);
                            v_items_3373_ = crate::leanh::lean_ctor_get(v_x_3332_, 0);
                            crate::leanh::lean_inc_ref(v_items_3373_);
                            crate::leanh::lean_dec_ref_known(v_x_3332_, 1);
                            v___x_3374_ = lean_array_get_size(v_items_3372_);
                            v___x_3375_ = lean_array_get_size(v_items_3373_);
                            v___x_3376_ = lean_nat_dec_eq(v___x_3374_, v___x_3375_);
                            if v___x_3376_ == 0 {
                                crate::leanh::lean_dec_ref(v_items_3373_);
                                crate::leanh::lean_dec_ref(v_items_3372_);
                                crate::leanh::lean_dec_ref(v_localinst_3333_);
                                crate::leanh::lean_dec_ref(v_inst_3329_);
                                return v___x_3376_;
                            } else {
                                v___x_3377_ = crate::leanh::lean_alloc_closure(
                                    l_Lean_Doc_instBEqInline_beq___boxed as *mut core::ffi::c_void,
                                    4,
                                    2,
                                );
                                crate::leanh::lean_closure_set(
                                    v___x_3377_,
                                    0,
                                    crate::leanh::lean_box(0),
                                );
                                crate::leanh::lean_closure_set(v___x_3377_, 1, v_inst_3329_);
                                v___x_3378_ = crate::leanh::lean_alloc_closure(
                                    l_Lean_Doc_instBEqDescItem_beq___boxed
                                        as *mut core::ffi::c_void,
                                    6,
                                    4,
                                );
                                crate::leanh::lean_closure_set(
                                    v___x_3378_,
                                    0,
                                    crate::leanh::lean_box(0),
                                );
                                crate::leanh::lean_closure_set(
                                    v___x_3378_,
                                    1,
                                    crate::leanh::lean_box(0),
                                );
                                crate::leanh::lean_closure_set(v___x_3378_, 2, v___x_3377_);
                                crate::leanh::lean_closure_set(v___x_3378_, 3, v_localinst_3333_);
                                v___x_3379_ = l_Array_isEqvAux___redArg(
                                    v_items_3372_,
                                    v_items_3373_,
                                    v___x_3378_,
                                    v___x_3374_,
                                );
                                crate::leanh::lean_dec_ref(v_items_3373_);
                                crate::leanh::lean_dec_ref(v_items_3372_);
                                return v___x_3379_;
                            }
                        } else {
                            crate::leanh::lean_dec_ref_known(v_x_3331_, 1);
                            crate::leanh::lean_dec_ref(v_localinst_3333_);
                            crate::leanh::lean_dec_ref(v_x_3332_);
                            crate::leanh::lean_dec_ref(v_inst_3329_);
                            v___x_3380_ = 0;
                            return v___x_3380_;
                        }
                    }
                    5 => {
                        crate::leanh::lean_dec_ref(v_inst_3330_);
                        crate::leanh::lean_dec_ref(v_inst_3329_);
                        if crate::leanh::lean_obj_tag(v_x_3332_) == 5 {
                            v_items_3381_ = crate::leanh::lean_ctor_get(v_x_3331_, 0);
                            crate::leanh::lean_inc_ref(v_items_3381_);
                            crate::leanh::lean_dec_ref_known(v_x_3331_, 1);
                            v_items_3382_ = crate::leanh::lean_ctor_get(v_x_3332_, 0);
                            crate::leanh::lean_inc_ref(v_items_3382_);
                            crate::leanh::lean_dec_ref_known(v_x_3332_, 1);
                            v_a_3335_ = v_items_3381_;
                            v_b_3336_ = v_items_3382_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_dec_ref_known(v_x_3331_, 1);
                            crate::leanh::lean_dec_ref(v_localinst_3333_);
                            crate::leanh::lean_dec_ref(v_x_3332_);
                            v___x_3383_ = 0;
                            return v___x_3383_;
                        }
                    }
                    6 => {
                        crate::leanh::lean_dec_ref(v_inst_3330_);
                        crate::leanh::lean_dec_ref(v_inst_3329_);
                        if crate::leanh::lean_obj_tag(v_x_3332_) == 6 {
                            v_content_3384_ = crate::leanh::lean_ctor_get(v_x_3331_, 0);
                            crate::leanh::lean_inc_ref(v_content_3384_);
                            crate::leanh::lean_dec_ref_known(v_x_3331_, 1);
                            v_content_3385_ = crate::leanh::lean_ctor_get(v_x_3332_, 0);
                            crate::leanh::lean_inc_ref(v_content_3385_);
                            crate::leanh::lean_dec_ref_known(v_x_3332_, 1);
                            v_a_3335_ = v_content_3384_;
                            v_b_3336_ = v_content_3385_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_dec_ref_known(v_x_3331_, 1);
                            crate::leanh::lean_dec_ref(v_localinst_3333_);
                            crate::leanh::lean_dec_ref(v_x_3332_);
                            v___x_3386_ = 0;
                            return v___x_3386_;
                        }
                    }
                    _ => {
                        crate::leanh::lean_dec_ref(v_inst_3329_);
                        if crate::leanh::lean_obj_tag(v_x_3332_) == 7 {
                            v_container_3387_ = crate::leanh::lean_ctor_get(v_x_3331_, 0);
                            crate::leanh::lean_inc(v_container_3387_);
                            v_content_3388_ = crate::leanh::lean_ctor_get(v_x_3331_, 1);
                            crate::leanh::lean_inc_ref(v_content_3388_);
                            crate::leanh::lean_dec_ref_known(v_x_3331_, 2);
                            v_container_3389_ = crate::leanh::lean_ctor_get(v_x_3332_, 0);
                            crate::leanh::lean_inc(v_container_3389_);
                            v_content_3390_ = crate::leanh::lean_ctor_get(v_x_3332_, 1);
                            crate::leanh::lean_inc_ref(v_content_3390_);
                            crate::leanh::lean_dec_ref_known(v_x_3332_, 2);
                            v___x_3391_ = crate::leanh::lean_apply_2(
                                v_inst_3330_,
                                v_container_3387_,
                                v_container_3389_,
                            );
                            v___x_3392_ = (crate::leanh::lean_unbox(v___x_3391_) as u8);
                            if v___x_3392_ == 0 {
                                crate::leanh::lean_dec_ref(v_content_3390_);
                                crate::leanh::lean_dec_ref(v_content_3388_);
                                crate::leanh::lean_dec_ref(v_localinst_3333_);
                                v___x_3393_ = (crate::leanh::lean_unbox(v___x_3391_) as u8);
                                return v___x_3393_;
                            } else {
                                v___x_3394_ = lean_array_get_size(v_content_3388_);
                                v___x_3395_ = lean_array_get_size(v_content_3390_);
                                v___x_3396_ = lean_nat_dec_eq(v___x_3394_, v___x_3395_);
                                if v___x_3396_ == 0 {
                                    crate::leanh::lean_dec_ref(v_content_3390_);
                                    crate::leanh::lean_dec_ref(v_content_3388_);
                                    crate::leanh::lean_dec_ref(v_localinst_3333_);
                                    return v___x_3396_;
                                } else {
                                    v___x_3397_ = l_Array_isEqvAux___redArg(
                                        v_content_3388_,
                                        v_content_3390_,
                                        v_localinst_3333_,
                                        v___x_3394_,
                                    );
                                    crate::leanh::lean_dec_ref(v_content_3390_);
                                    crate::leanh::lean_dec_ref(v_content_3388_);
                                    return v___x_3397_;
                                }
                            }
                        } else {
                            crate::leanh::lean_dec_ref_known(v_x_3331_, 2);
                            crate::leanh::lean_dec_ref(v_localinst_3333_);
                            crate::leanh::lean_dec_ref(v_x_3332_);
                            crate::leanh::lean_dec_ref(v_inst_3330_);
                            v___x_3398_ = 0;
                            return v___x_3398_;
                        }
                    }
                }
            }
            1 => {
                v___x_3337_ = lean_array_get_size(v_a_3335_);
                v___x_3338_ = lean_array_get_size(v_b_3336_);
                v___x_3339_ = lean_nat_dec_eq(v___x_3337_, v___x_3338_);
                if v___x_3339_ == 0 {
                    crate::leanh::lean_dec_ref(v_b_3336_);
                    crate::leanh::lean_dec_ref(v_a_3335_);
                    crate::leanh::lean_dec_ref(v_localinst_3333_);
                    return v___x_3339_;
                } else {
                    v___x_3340_ = l_Array_isEqvAux___redArg(
                        v_a_3335_,
                        v_b_3336_,
                        v_localinst_3333_,
                        v___x_3337_,
                    );
                    crate::leanh::lean_dec_ref(v_b_3336_);
                    crate::leanh::lean_dec_ref(v_a_3335_);
                    return v___x_3340_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Doc_instBEqBlock_beq(
    mut v_i_3399_: *mut crate::leanh::LeanObject,
    mut v_b_3400_: *mut crate::leanh::LeanObject,
    mut v_inst_3401_: *mut crate::leanh::LeanObject,
    mut v_inst_3402_: *mut crate::leanh::LeanObject,
    mut v_x_3403_: *mut crate::leanh::LeanObject,
    mut v_x_3404_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_3405_: u8 = 0;
    v___x_3405_ =
        l_Lean_Doc_instBEqBlock_beq___redArg(v_inst_3401_, v_inst_3402_, v_x_3403_, v_x_3404_);
    return v___x_3405_;
}
pub unsafe fn l_Lean_Doc_instBEqBlock_beq___boxed(
    mut v_i_3406_: *mut crate::leanh::LeanObject,
    mut v_b_3407_: *mut crate::leanh::LeanObject,
    mut v_inst_3408_: *mut crate::leanh::LeanObject,
    mut v_inst_3409_: *mut crate::leanh::LeanObject,
    mut v_x_3410_: *mut crate::leanh::LeanObject,
    mut v_x_3411_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3412_: u8 = 0;
    let mut v_r_3413_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3412_ = l_Lean_Doc_instBEqBlock_beq(
        v_i_3406_,
        v_b_3407_,
        v_inst_3408_,
        v_inst_3409_,
        v_x_3410_,
        v_x_3411_,
    );
    v_r_3413_ = crate::leanh::lean_box((v_res_3412_) as usize);
    return v_r_3413_;
}
pub unsafe fn l_Lean_Doc_instBEqBlock___redArg(
    mut v_inst_3414_: *mut crate::leanh::LeanObject,
    mut v_inst_3415_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3416_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3416_ = crate::leanh::lean_alloc_closure(
        l_Lean_Doc_instBEqBlock_beq___boxed as *mut core::ffi::c_void,
        6,
        4,
    );
    crate::leanh::lean_closure_set(v___x_3416_, 0, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_3416_, 1, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_3416_, 2, v_inst_3414_);
    crate::leanh::lean_closure_set(v___x_3416_, 3, v_inst_3415_);
    return v___x_3416_;
}
pub unsafe fn l_Lean_Doc_instBEqBlock(
    mut v_i_3417_: *mut crate::leanh::LeanObject,
    mut v_b_3418_: *mut crate::leanh::LeanObject,
    mut v_inst_3419_: *mut crate::leanh::LeanObject,
    mut v_inst_3420_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3421_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3421_ = crate::leanh::lean_alloc_closure(
        l_Lean_Doc_instBEqBlock_beq___boxed as *mut core::ffi::c_void,
        6,
        4,
    );
    crate::leanh::lean_closure_set(v___x_3421_, 0, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_3421_, 1, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_3421_, 2, v_inst_3419_);
    crate::leanh::lean_closure_set(v___x_3421_, 3, v_inst_3420_);
    return v___x_3421_;
}
pub unsafe fn l_Lean_Doc_instOrdBlock_ord___redArg___boxed(
    mut v_inst_3422_: *mut crate::leanh::LeanObject,
    mut v_inst_3423_: *mut crate::leanh::LeanObject,
    mut v_x_3424_: *mut crate::leanh::LeanObject,
    mut v_x_3425_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3426_: u8 = 0;
    let mut v_r_3427_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3426_ =
        l_Lean_Doc_instOrdBlock_ord___redArg(v_inst_3422_, v_inst_3423_, v_x_3424_, v_x_3425_);
    v_r_3427_ = crate::leanh::lean_box((v_res_3426_) as usize);
    return v_r_3427_;
}
pub unsafe fn l_Lean_Doc_instOrdBlock_ord___redArg(
    mut v_inst_3428_: *mut crate::leanh::LeanObject,
    mut v_inst_3429_: *mut crate::leanh::LeanObject,
    mut v_x_3430_: *mut crate::leanh::LeanObject,
    mut v_x_3431_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v_localinst_3432_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3434_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_b_3435_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3436_: u8 = 0;
    let mut v_contents_3437_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_contents_3438_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3439_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3440_: u8 = 0;
    let mut v___x_3441_: u8 = 0;
    let mut v___x_3442_: u8 = 0;
    let mut v___x_3443_: u8 = 0;
    let mut v___x_3444_: u8 = 0;
    let mut v___x_3445_: u8 = 0;
    let mut v___x_3446_: u8 = 0;
    let mut v___x_3447_: u8 = 0;
    let mut v___x_3448_: u8 = 0;
    let mut v_content_3449_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_content_3450_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3451_: u8 = 0;
    let mut v___x_3452_: u8 = 0;
    let mut v___x_3453_: u8 = 0;
    let mut v___x_3454_: u8 = 0;
    let mut v___x_3455_: u8 = 0;
    let mut v___x_3456_: u8 = 0;
    let mut v___x_3457_: u8 = 0;
    let mut v___x_3458_: u8 = 0;
    let mut v___x_3459_: u8 = 0;
    let mut v_items_3460_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_items_3461_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3462_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3463_: u8 = 0;
    let mut v___x_3464_: u8 = 0;
    let mut v___x_3465_: u8 = 0;
    let mut v___x_3466_: u8 = 0;
    let mut v___x_3467_: u8 = 0;
    let mut v___x_3468_: u8 = 0;
    let mut v___x_3469_: u8 = 0;
    let mut v___x_3470_: u8 = 0;
    let mut v___x_3471_: u8 = 0;
    let mut v_start_3472_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_items_3473_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_start_3474_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_items_3475_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3476_: u8 = 0;
    let mut v___x_3477_: u8 = 0;
    let mut v___x_3478_: u8 = 0;
    let mut v___x_3479_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3480_: u8 = 0;
    let mut v___x_3481_: u8 = 0;
    let mut v___x_3482_: u8 = 0;
    let mut v___x_3483_: u8 = 0;
    let mut v___x_3484_: u8 = 0;
    let mut v___x_3485_: u8 = 0;
    let mut v___x_3486_: u8 = 0;
    let mut v___x_3487_: u8 = 0;
    let mut v___x_3488_: u8 = 0;
    let mut v___x_3489_: u8 = 0;
    let mut v_items_3490_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_items_3491_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3492_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3493_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3494_: u8 = 0;
    let mut v___x_3495_: u8 = 0;
    let mut v___x_3496_: u8 = 0;
    let mut v___x_3497_: u8 = 0;
    let mut v___x_3498_: u8 = 0;
    let mut v___x_3499_: u8 = 0;
    let mut v___x_3500_: u8 = 0;
    let mut v___x_3501_: u8 = 0;
    let mut v___x_3502_: u8 = 0;
    let mut v_items_3503_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_items_3504_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3505_: u8 = 0;
    let mut v___x_3506_: u8 = 0;
    let mut v___x_3507_: u8 = 0;
    let mut v___x_3508_: u8 = 0;
    let mut v___x_3509_: u8 = 0;
    let mut v___x_3510_: u8 = 0;
    let mut v___x_3511_: u8 = 0;
    let mut v___x_3512_: u8 = 0;
    let mut v_content_3513_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_content_3514_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3515_: u8 = 0;
    let mut v_container_3516_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_content_3517_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_container_3518_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_content_3519_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3520_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3521_: u8 = 0;
    let mut v___x_3522_: u8 = 0;
    let mut v___x_3523_: u8 = 0;
    let mut v___x_3524_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                crate::leanh::lean_inc_ref(v_inst_3429_);
                crate::leanh::lean_inc_ref(v_inst_3428_);
                v_localinst_3432_ = crate::leanh::lean_alloc_closure(
                    l_Lean_Doc_instOrdBlock_ord___redArg___boxed as *mut core::ffi::c_void,
                    4,
                    2,
                );
                crate::leanh::lean_closure_set(v_localinst_3432_, 0, v_inst_3428_);
                crate::leanh::lean_closure_set(v_localinst_3432_, 1, v_inst_3429_);
                match crate::leanh::lean_obj_tag(v_x_3430_) {
                    0 => {
                        crate::leanh::lean_dec_ref(v_localinst_3432_);
                        crate::leanh::lean_dec_ref(v_inst_3429_);
                        match crate::leanh::lean_obj_tag(v_x_3431_) {
                            0 => {
                                v_contents_3437_ = crate::leanh::lean_ctor_get(v_x_3430_, 0);
                                crate::leanh::lean_inc_ref(v_contents_3437_);
                                crate::leanh::lean_dec_ref_known(v_x_3430_, 1);
                                v_contents_3438_ = crate::leanh::lean_ctor_get(v_x_3431_, 0);
                                crate::leanh::lean_inc_ref(v_contents_3438_);
                                crate::leanh::lean_dec_ref_known(v_x_3431_, 1);
                                v___x_3439_ = crate::leanh::lean_alloc_closure(
                                    l_Lean_Doc_instOrdInline_ord___boxed as *mut core::ffi::c_void,
                                    4,
                                    2,
                                );
                                crate::leanh::lean_closure_set(
                                    v___x_3439_,
                                    0,
                                    crate::leanh::lean_box(0),
                                );
                                crate::leanh::lean_closure_set(v___x_3439_, 1, v_inst_3428_);
                                v___x_3440_ = l_Array_compareLex___redArg(
                                    v___x_3439_,
                                    v_contents_3437_,
                                    v_contents_3438_,
                                );
                                crate::leanh::lean_dec_ref(v_contents_3438_);
                                crate::leanh::lean_dec_ref(v_contents_3437_);
                                if v___x_3440_ == 1 {
                                    return v___x_3440_;
                                } else {
                                    return v___x_3440_;
                                }
                            }
                            1 => {
                                crate::leanh::lean_dec_ref_known(v_x_3431_, 1);
                                crate::leanh::lean_dec_ref_known(v_x_3430_, 1);
                                crate::leanh::lean_dec_ref(v_inst_3428_);
                                v___x_3441_ = 0;
                                return v___x_3441_;
                            }
                            2 => {
                                crate::leanh::lean_dec_ref_known(v_x_3431_, 1);
                                crate::leanh::lean_dec_ref_known(v_x_3430_, 1);
                                crate::leanh::lean_dec_ref(v_inst_3428_);
                                v___x_3442_ = 0;
                                return v___x_3442_;
                            }
                            3 => {
                                crate::leanh::lean_dec_ref_known(v_x_3431_, 2);
                                crate::leanh::lean_dec_ref_known(v_x_3430_, 1);
                                crate::leanh::lean_dec_ref(v_inst_3428_);
                                v___x_3443_ = 0;
                                return v___x_3443_;
                            }
                            4 => {
                                crate::leanh::lean_dec_ref_known(v_x_3431_, 1);
                                crate::leanh::lean_dec_ref_known(v_x_3430_, 1);
                                crate::leanh::lean_dec_ref(v_inst_3428_);
                                v___x_3444_ = 0;
                                return v___x_3444_;
                            }
                            5 => {
                                crate::leanh::lean_dec_ref_known(v_x_3431_, 1);
                                crate::leanh::lean_dec_ref_known(v_x_3430_, 1);
                                crate::leanh::lean_dec_ref(v_inst_3428_);
                                v___x_3445_ = 0;
                                return v___x_3445_;
                            }
                            6 => {
                                crate::leanh::lean_dec_ref_known(v_x_3431_, 1);
                                crate::leanh::lean_dec_ref_known(v_x_3430_, 1);
                                crate::leanh::lean_dec_ref(v_inst_3428_);
                                v___x_3446_ = 0;
                                return v___x_3446_;
                            }
                            _ => {
                                crate::leanh::lean_dec_ref_known(v_x_3430_, 1);
                                crate::leanh::lean_dec_ref(v_x_3431_);
                                crate::leanh::lean_dec_ref(v_inst_3428_);
                                v___x_3447_ = 0;
                                return v___x_3447_;
                            }
                        }
                    }
                    1 => {
                        crate::leanh::lean_dec_ref(v_localinst_3432_);
                        crate::leanh::lean_dec_ref(v_inst_3429_);
                        crate::leanh::lean_dec_ref(v_inst_3428_);
                        match crate::leanh::lean_obj_tag(v_x_3431_) {
                            0 => {
                                crate::leanh::lean_dec_ref_known(v_x_3431_, 1);
                                crate::leanh::lean_dec_ref_known(v_x_3430_, 1);
                                v___x_3448_ = 2;
                                return v___x_3448_;
                            }
                            1 => {
                                v_content_3449_ = crate::leanh::lean_ctor_get(v_x_3430_, 0);
                                crate::leanh::lean_inc_ref(v_content_3449_);
                                crate::leanh::lean_dec_ref_known(v_x_3430_, 1);
                                v_content_3450_ = crate::leanh::lean_ctor_get(v_x_3431_, 0);
                                crate::leanh::lean_inc_ref(v_content_3450_);
                                crate::leanh::lean_dec_ref_known(v_x_3431_, 1);
                                v___x_3451_ = lean_string_compare(v_content_3449_, v_content_3450_);
                                crate::leanh::lean_dec_ref(v_content_3450_);
                                crate::leanh::lean_dec_ref(v_content_3449_);
                                if v___x_3451_ == 1 {
                                    return v___x_3451_;
                                } else {
                                    return v___x_3451_;
                                }
                            }
                            2 => {
                                crate::leanh::lean_dec_ref_known(v_x_3431_, 1);
                                crate::leanh::lean_dec_ref_known(v_x_3430_, 1);
                                v___x_3452_ = 0;
                                return v___x_3452_;
                            }
                            3 => {
                                crate::leanh::lean_dec_ref_known(v_x_3431_, 2);
                                crate::leanh::lean_dec_ref_known(v_x_3430_, 1);
                                v___x_3453_ = 0;
                                return v___x_3453_;
                            }
                            4 => {
                                crate::leanh::lean_dec_ref_known(v_x_3431_, 1);
                                crate::leanh::lean_dec_ref_known(v_x_3430_, 1);
                                v___x_3454_ = 0;
                                return v___x_3454_;
                            }
                            5 => {
                                crate::leanh::lean_dec_ref_known(v_x_3431_, 1);
                                crate::leanh::lean_dec_ref_known(v_x_3430_, 1);
                                v___x_3455_ = 0;
                                return v___x_3455_;
                            }
                            6 => {
                                crate::leanh::lean_dec_ref_known(v_x_3431_, 1);
                                crate::leanh::lean_dec_ref_known(v_x_3430_, 1);
                                v___x_3456_ = 0;
                                return v___x_3456_;
                            }
                            _ => {
                                crate::leanh::lean_dec_ref_known(v_x_3430_, 1);
                                crate::leanh::lean_dec_ref(v_x_3431_);
                                v___x_3457_ = 0;
                                return v___x_3457_;
                            }
                        }
                    }
                    2 => {
                        crate::leanh::lean_dec_ref(v_inst_3429_);
                        crate::leanh::lean_dec_ref(v_inst_3428_);
                        match crate::leanh::lean_obj_tag(v_x_3431_) {
                            0 => {
                                crate::leanh::lean_dec_ref_known(v_x_3431_, 1);
                                crate::leanh::lean_dec_ref_known(v_x_3430_, 1);
                                crate::leanh::lean_dec_ref(v_localinst_3432_);
                                v___x_3458_ = 2;
                                return v___x_3458_;
                            }
                            1 => {
                                crate::leanh::lean_dec_ref_known(v_x_3431_, 1);
                                crate::leanh::lean_dec_ref_known(v_x_3430_, 1);
                                crate::leanh::lean_dec_ref(v_localinst_3432_);
                                v___x_3459_ = 2;
                                return v___x_3459_;
                            }
                            2 => {
                                v_items_3460_ = crate::leanh::lean_ctor_get(v_x_3430_, 0);
                                crate::leanh::lean_inc_ref(v_items_3460_);
                                crate::leanh::lean_dec_ref_known(v_x_3430_, 1);
                                v_items_3461_ = crate::leanh::lean_ctor_get(v_x_3431_, 0);
                                crate::leanh::lean_inc_ref(v_items_3461_);
                                crate::leanh::lean_dec_ref_known(v_x_3431_, 1);
                                v___x_3462_ = crate::leanh::lean_alloc_closure(
                                    l_Lean_Doc_instOrdListItem_ord___boxed
                                        as *mut core::ffi::c_void,
                                    4,
                                    2,
                                );
                                crate::leanh::lean_closure_set(
                                    v___x_3462_,
                                    0,
                                    crate::leanh::lean_box(0),
                                );
                                crate::leanh::lean_closure_set(v___x_3462_, 1, v_localinst_3432_);
                                v___x_3463_ = l_Array_compareLex___redArg(
                                    v___x_3462_,
                                    v_items_3460_,
                                    v_items_3461_,
                                );
                                crate::leanh::lean_dec_ref(v_items_3461_);
                                crate::leanh::lean_dec_ref(v_items_3460_);
                                if v___x_3463_ == 1 {
                                    return v___x_3463_;
                                } else {
                                    return v___x_3463_;
                                }
                            }
                            3 => {
                                crate::leanh::lean_dec_ref_known(v_x_3431_, 2);
                                crate::leanh::lean_dec_ref_known(v_x_3430_, 1);
                                crate::leanh::lean_dec_ref(v_localinst_3432_);
                                v___x_3464_ = 0;
                                return v___x_3464_;
                            }
                            4 => {
                                crate::leanh::lean_dec_ref_known(v_x_3431_, 1);
                                crate::leanh::lean_dec_ref_known(v_x_3430_, 1);
                                crate::leanh::lean_dec_ref(v_localinst_3432_);
                                v___x_3465_ = 0;
                                return v___x_3465_;
                            }
                            5 => {
                                crate::leanh::lean_dec_ref_known(v_x_3431_, 1);
                                crate::leanh::lean_dec_ref_known(v_x_3430_, 1);
                                crate::leanh::lean_dec_ref(v_localinst_3432_);
                                v___x_3466_ = 0;
                                return v___x_3466_;
                            }
                            6 => {
                                crate::leanh::lean_dec_ref_known(v_x_3431_, 1);
                                crate::leanh::lean_dec_ref_known(v_x_3430_, 1);
                                crate::leanh::lean_dec_ref(v_localinst_3432_);
                                v___x_3467_ = 0;
                                return v___x_3467_;
                            }
                            _ => {
                                crate::leanh::lean_dec_ref_known(v_x_3430_, 1);
                                crate::leanh::lean_dec_ref(v_localinst_3432_);
                                crate::leanh::lean_dec_ref(v_x_3431_);
                                v___x_3468_ = 0;
                                return v___x_3468_;
                            }
                        }
                    }
                    3 => {
                        crate::leanh::lean_dec_ref(v_inst_3429_);
                        crate::leanh::lean_dec_ref(v_inst_3428_);
                        match crate::leanh::lean_obj_tag(v_x_3431_) {
                            0 => {
                                crate::leanh::lean_dec_ref_known(v_x_3431_, 1);
                                crate::leanh::lean_dec_ref_known(v_x_3430_, 2);
                                crate::leanh::lean_dec_ref(v_localinst_3432_);
                                v___x_3469_ = 2;
                                return v___x_3469_;
                            }
                            1 => {
                                crate::leanh::lean_dec_ref_known(v_x_3431_, 1);
                                crate::leanh::lean_dec_ref_known(v_x_3430_, 2);
                                crate::leanh::lean_dec_ref(v_localinst_3432_);
                                v___x_3470_ = 2;
                                return v___x_3470_;
                            }
                            2 => {
                                crate::leanh::lean_dec_ref_known(v_x_3431_, 1);
                                crate::leanh::lean_dec_ref_known(v_x_3430_, 2);
                                crate::leanh::lean_dec_ref(v_localinst_3432_);
                                v___x_3471_ = 2;
                                return v___x_3471_;
                            }
                            3 => {
                                v_start_3472_ = crate::leanh::lean_ctor_get(v_x_3430_, 0);
                                crate::leanh::lean_inc(v_start_3472_);
                                v_items_3473_ = crate::leanh::lean_ctor_get(v_x_3430_, 1);
                                crate::leanh::lean_inc_ref(v_items_3473_);
                                crate::leanh::lean_dec_ref_known(v_x_3430_, 2);
                                v_start_3474_ = crate::leanh::lean_ctor_get(v_x_3431_, 0);
                                crate::leanh::lean_inc(v_start_3474_);
                                v_items_3475_ = crate::leanh::lean_ctor_get(v_x_3431_, 1);
                                crate::leanh::lean_inc_ref(v_items_3475_);
                                crate::leanh::lean_dec_ref_known(v_x_3431_, 2);
                                v___x_3476_ = lean_int_dec_lt(v_start_3472_, v_start_3474_);
                                if v___x_3476_ == 0 {
                                    v___x_3477_ = lean_int_dec_eq(v_start_3472_, v_start_3474_);
                                    crate::leanh::lean_dec(v_start_3474_);
                                    crate::leanh::lean_dec(v_start_3472_);
                                    if v___x_3477_ == 0 {
                                        crate::leanh::lean_dec_ref(v_items_3475_);
                                        crate::leanh::lean_dec_ref(v_items_3473_);
                                        crate::leanh::lean_dec_ref(v_localinst_3432_);
                                        v___x_3478_ = 2;
                                        return v___x_3478_;
                                    } else {
                                        v___x_3479_ = crate::leanh::lean_alloc_closure(
                                            l_Lean_Doc_instOrdListItem_ord___boxed
                                                as *mut core::ffi::c_void,
                                            4,
                                            2,
                                        );
                                        crate::leanh::lean_closure_set(
                                            v___x_3479_,
                                            0,
                                            crate::leanh::lean_box(0),
                                        );
                                        crate::leanh::lean_closure_set(
                                            v___x_3479_,
                                            1,
                                            v_localinst_3432_,
                                        );
                                        v___x_3480_ = l_Array_compareLex___redArg(
                                            v___x_3479_,
                                            v_items_3473_,
                                            v_items_3475_,
                                        );
                                        crate::leanh::lean_dec_ref(v_items_3475_);
                                        crate::leanh::lean_dec_ref(v_items_3473_);
                                        if v___x_3480_ == 1 {
                                            return v___x_3480_;
                                        } else {
                                            return v___x_3480_;
                                        }
                                    }
                                } else {
                                    crate::leanh::lean_dec_ref(v_items_3475_);
                                    crate::leanh::lean_dec(v_start_3474_);
                                    crate::leanh::lean_dec_ref(v_items_3473_);
                                    crate::leanh::lean_dec(v_start_3472_);
                                    crate::leanh::lean_dec_ref(v_localinst_3432_);
                                    v___x_3481_ = 0;
                                    return v___x_3481_;
                                }
                            }
                            4 => {
                                crate::leanh::lean_dec_ref_known(v_x_3431_, 1);
                                crate::leanh::lean_dec_ref_known(v_x_3430_, 2);
                                crate::leanh::lean_dec_ref(v_localinst_3432_);
                                v___x_3482_ = 0;
                                return v___x_3482_;
                            }
                            5 => {
                                crate::leanh::lean_dec_ref_known(v_x_3431_, 1);
                                crate::leanh::lean_dec_ref_known(v_x_3430_, 2);
                                crate::leanh::lean_dec_ref(v_localinst_3432_);
                                v___x_3483_ = 0;
                                return v___x_3483_;
                            }
                            6 => {
                                crate::leanh::lean_dec_ref_known(v_x_3431_, 1);
                                crate::leanh::lean_dec_ref_known(v_x_3430_, 2);
                                crate::leanh::lean_dec_ref(v_localinst_3432_);
                                v___x_3484_ = 0;
                                return v___x_3484_;
                            }
                            _ => {
                                crate::leanh::lean_dec_ref_known(v_x_3430_, 2);
                                crate::leanh::lean_dec_ref(v_localinst_3432_);
                                crate::leanh::lean_dec_ref(v_x_3431_);
                                v___x_3485_ = 0;
                                return v___x_3485_;
                            }
                        }
                    }
                    4 => {
                        crate::leanh::lean_dec_ref(v_inst_3429_);
                        match crate::leanh::lean_obj_tag(v_x_3431_) {
                            0 => {
                                crate::leanh::lean_dec_ref_known(v_x_3431_, 1);
                                crate::leanh::lean_dec_ref_known(v_x_3430_, 1);
                                crate::leanh::lean_dec_ref(v_localinst_3432_);
                                crate::leanh::lean_dec_ref(v_inst_3428_);
                                v___x_3486_ = 2;
                                return v___x_3486_;
                            }
                            1 => {
                                crate::leanh::lean_dec_ref_known(v_x_3431_, 1);
                                crate::leanh::lean_dec_ref_known(v_x_3430_, 1);
                                crate::leanh::lean_dec_ref(v_localinst_3432_);
                                crate::leanh::lean_dec_ref(v_inst_3428_);
                                v___x_3487_ = 2;
                                return v___x_3487_;
                            }
                            2 => {
                                crate::leanh::lean_dec_ref_known(v_x_3431_, 1);
                                crate::leanh::lean_dec_ref_known(v_x_3430_, 1);
                                crate::leanh::lean_dec_ref(v_localinst_3432_);
                                crate::leanh::lean_dec_ref(v_inst_3428_);
                                v___x_3488_ = 2;
                                return v___x_3488_;
                            }
                            3 => {
                                crate::leanh::lean_dec_ref_known(v_x_3431_, 2);
                                crate::leanh::lean_dec_ref_known(v_x_3430_, 1);
                                crate::leanh::lean_dec_ref(v_localinst_3432_);
                                crate::leanh::lean_dec_ref(v_inst_3428_);
                                v___x_3489_ = 2;
                                return v___x_3489_;
                            }
                            4 => {
                                v_items_3490_ = crate::leanh::lean_ctor_get(v_x_3430_, 0);
                                crate::leanh::lean_inc_ref(v_items_3490_);
                                crate::leanh::lean_dec_ref_known(v_x_3430_, 1);
                                v_items_3491_ = crate::leanh::lean_ctor_get(v_x_3431_, 0);
                                crate::leanh::lean_inc_ref(v_items_3491_);
                                crate::leanh::lean_dec_ref_known(v_x_3431_, 1);
                                v___x_3492_ = crate::leanh::lean_alloc_closure(
                                    l_Lean_Doc_instOrdInline_ord___boxed as *mut core::ffi::c_void,
                                    4,
                                    2,
                                );
                                crate::leanh::lean_closure_set(
                                    v___x_3492_,
                                    0,
                                    crate::leanh::lean_box(0),
                                );
                                crate::leanh::lean_closure_set(v___x_3492_, 1, v_inst_3428_);
                                v___x_3493_ = crate::leanh::lean_alloc_closure(
                                    l_Lean_Doc_instOrdDescItem_ord___boxed
                                        as *mut core::ffi::c_void,
                                    6,
                                    4,
                                );
                                crate::leanh::lean_closure_set(
                                    v___x_3493_,
                                    0,
                                    crate::leanh::lean_box(0),
                                );
                                crate::leanh::lean_closure_set(
                                    v___x_3493_,
                                    1,
                                    crate::leanh::lean_box(0),
                                );
                                crate::leanh::lean_closure_set(v___x_3493_, 2, v___x_3492_);
                                crate::leanh::lean_closure_set(v___x_3493_, 3, v_localinst_3432_);
                                v___x_3494_ = l_Array_compareLex___redArg(
                                    v___x_3493_,
                                    v_items_3490_,
                                    v_items_3491_,
                                );
                                crate::leanh::lean_dec_ref(v_items_3491_);
                                crate::leanh::lean_dec_ref(v_items_3490_);
                                if v___x_3494_ == 1 {
                                    return v___x_3494_;
                                } else {
                                    return v___x_3494_;
                                }
                            }
                            5 => {
                                crate::leanh::lean_dec_ref_known(v_x_3431_, 1);
                                crate::leanh::lean_dec_ref_known(v_x_3430_, 1);
                                crate::leanh::lean_dec_ref(v_localinst_3432_);
                                crate::leanh::lean_dec_ref(v_inst_3428_);
                                v___x_3495_ = 0;
                                return v___x_3495_;
                            }
                            6 => {
                                crate::leanh::lean_dec_ref_known(v_x_3431_, 1);
                                crate::leanh::lean_dec_ref_known(v_x_3430_, 1);
                                crate::leanh::lean_dec_ref(v_localinst_3432_);
                                crate::leanh::lean_dec_ref(v_inst_3428_);
                                v___x_3496_ = 0;
                                return v___x_3496_;
                            }
                            _ => {
                                crate::leanh::lean_dec_ref_known(v_x_3430_, 1);
                                crate::leanh::lean_dec_ref(v_localinst_3432_);
                                crate::leanh::lean_dec_ref(v_x_3431_);
                                crate::leanh::lean_dec_ref(v_inst_3428_);
                                v___x_3497_ = 0;
                                return v___x_3497_;
                            }
                        }
                    }
                    5 => {
                        crate::leanh::lean_dec_ref(v_inst_3429_);
                        crate::leanh::lean_dec_ref(v_inst_3428_);
                        match crate::leanh::lean_obj_tag(v_x_3431_) {
                            0 => {
                                crate::leanh::lean_dec_ref_known(v_x_3431_, 1);
                                crate::leanh::lean_dec_ref_known(v_x_3430_, 1);
                                crate::leanh::lean_dec_ref(v_localinst_3432_);
                                v___x_3498_ = 2;
                                return v___x_3498_;
                            }
                            1 => {
                                crate::leanh::lean_dec_ref_known(v_x_3431_, 1);
                                crate::leanh::lean_dec_ref_known(v_x_3430_, 1);
                                crate::leanh::lean_dec_ref(v_localinst_3432_);
                                v___x_3499_ = 2;
                                return v___x_3499_;
                            }
                            2 => {
                                crate::leanh::lean_dec_ref_known(v_x_3431_, 1);
                                crate::leanh::lean_dec_ref_known(v_x_3430_, 1);
                                crate::leanh::lean_dec_ref(v_localinst_3432_);
                                v___x_3500_ = 2;
                                return v___x_3500_;
                            }
                            3 => {
                                crate::leanh::lean_dec_ref_known(v_x_3431_, 2);
                                crate::leanh::lean_dec_ref_known(v_x_3430_, 1);
                                crate::leanh::lean_dec_ref(v_localinst_3432_);
                                v___x_3501_ = 2;
                                return v___x_3501_;
                            }
                            4 => {
                                crate::leanh::lean_dec_ref_known(v_x_3431_, 1);
                                crate::leanh::lean_dec_ref_known(v_x_3430_, 1);
                                crate::leanh::lean_dec_ref(v_localinst_3432_);
                                v___x_3502_ = 2;
                                return v___x_3502_;
                            }
                            5 => {
                                v_items_3503_ = crate::leanh::lean_ctor_get(v_x_3430_, 0);
                                crate::leanh::lean_inc_ref(v_items_3503_);
                                crate::leanh::lean_dec_ref_known(v_x_3430_, 1);
                                v_items_3504_ = crate::leanh::lean_ctor_get(v_x_3431_, 0);
                                crate::leanh::lean_inc_ref(v_items_3504_);
                                crate::leanh::lean_dec_ref_known(v_x_3431_, 1);
                                v_a_3434_ = v_items_3503_;
                                v_b_3435_ = v_items_3504_;
                                state = 1;
                                continue;
                            }
                            6 => {
                                crate::leanh::lean_dec_ref_known(v_x_3431_, 1);
                                crate::leanh::lean_dec_ref_known(v_x_3430_, 1);
                                crate::leanh::lean_dec_ref(v_localinst_3432_);
                                v___x_3505_ = 0;
                                return v___x_3505_;
                            }
                            _ => {
                                crate::leanh::lean_dec_ref_known(v_x_3430_, 1);
                                crate::leanh::lean_dec_ref(v_localinst_3432_);
                                crate::leanh::lean_dec_ref(v_x_3431_);
                                v___x_3506_ = 0;
                                return v___x_3506_;
                            }
                        }
                    }
                    6 => {
                        crate::leanh::lean_dec_ref(v_inst_3429_);
                        crate::leanh::lean_dec_ref(v_inst_3428_);
                        match crate::leanh::lean_obj_tag(v_x_3431_) {
                            0 => {
                                crate::leanh::lean_dec_ref_known(v_x_3431_, 1);
                                crate::leanh::lean_dec_ref_known(v_x_3430_, 1);
                                crate::leanh::lean_dec_ref(v_localinst_3432_);
                                v___x_3507_ = 2;
                                return v___x_3507_;
                            }
                            1 => {
                                crate::leanh::lean_dec_ref_known(v_x_3431_, 1);
                                crate::leanh::lean_dec_ref_known(v_x_3430_, 1);
                                crate::leanh::lean_dec_ref(v_localinst_3432_);
                                v___x_3508_ = 2;
                                return v___x_3508_;
                            }
                            2 => {
                                crate::leanh::lean_dec_ref_known(v_x_3431_, 1);
                                crate::leanh::lean_dec_ref_known(v_x_3430_, 1);
                                crate::leanh::lean_dec_ref(v_localinst_3432_);
                                v___x_3509_ = 2;
                                return v___x_3509_;
                            }
                            3 => {
                                crate::leanh::lean_dec_ref_known(v_x_3431_, 2);
                                crate::leanh::lean_dec_ref_known(v_x_3430_, 1);
                                crate::leanh::lean_dec_ref(v_localinst_3432_);
                                v___x_3510_ = 2;
                                return v___x_3510_;
                            }
                            4 => {
                                crate::leanh::lean_dec_ref_known(v_x_3431_, 1);
                                crate::leanh::lean_dec_ref_known(v_x_3430_, 1);
                                crate::leanh::lean_dec_ref(v_localinst_3432_);
                                v___x_3511_ = 2;
                                return v___x_3511_;
                            }
                            5 => {
                                crate::leanh::lean_dec_ref_known(v_x_3431_, 1);
                                crate::leanh::lean_dec_ref_known(v_x_3430_, 1);
                                crate::leanh::lean_dec_ref(v_localinst_3432_);
                                v___x_3512_ = 2;
                                return v___x_3512_;
                            }
                            6 => {
                                v_content_3513_ = crate::leanh::lean_ctor_get(v_x_3430_, 0);
                                crate::leanh::lean_inc_ref(v_content_3513_);
                                crate::leanh::lean_dec_ref_known(v_x_3430_, 1);
                                v_content_3514_ = crate::leanh::lean_ctor_get(v_x_3431_, 0);
                                crate::leanh::lean_inc_ref(v_content_3514_);
                                crate::leanh::lean_dec_ref_known(v_x_3431_, 1);
                                v_a_3434_ = v_content_3513_;
                                v_b_3435_ = v_content_3514_;
                                state = 1;
                                continue;
                            }
                            _ => {
                                crate::leanh::lean_dec_ref_known(v_x_3430_, 1);
                                crate::leanh::lean_dec_ref(v_localinst_3432_);
                                crate::leanh::lean_dec_ref(v_x_3431_);
                                v___x_3515_ = 0;
                                return v___x_3515_;
                            }
                        }
                    }
                    _ => {
                        crate::leanh::lean_dec_ref(v_inst_3428_);
                        if crate::leanh::lean_obj_tag(v_x_3431_) == 7 {
                            v_container_3516_ = crate::leanh::lean_ctor_get(v_x_3430_, 0);
                            crate::leanh::lean_inc(v_container_3516_);
                            v_content_3517_ = crate::leanh::lean_ctor_get(v_x_3430_, 1);
                            crate::leanh::lean_inc_ref(v_content_3517_);
                            crate::leanh::lean_dec_ref_known(v_x_3430_, 2);
                            v_container_3518_ = crate::leanh::lean_ctor_get(v_x_3431_, 0);
                            crate::leanh::lean_inc(v_container_3518_);
                            v_content_3519_ = crate::leanh::lean_ctor_get(v_x_3431_, 1);
                            crate::leanh::lean_inc_ref(v_content_3519_);
                            crate::leanh::lean_dec_ref_known(v_x_3431_, 2);
                            v___x_3520_ = crate::leanh::lean_apply_2(
                                v_inst_3429_,
                                v_container_3516_,
                                v_container_3518_,
                            );
                            v___x_3521_ = (crate::leanh::lean_unbox(v___x_3520_) as u8);
                            if v___x_3521_ == 1 {
                                v___x_3522_ = l_Array_compareLex___redArg(
                                    v_localinst_3432_,
                                    v_content_3517_,
                                    v_content_3519_,
                                );
                                crate::leanh::lean_dec_ref(v_content_3519_);
                                crate::leanh::lean_dec_ref(v_content_3517_);
                                if v___x_3522_ == 1 {
                                    return v___x_3522_;
                                } else {
                                    return v___x_3522_;
                                }
                            } else {
                                crate::leanh::lean_dec_ref(v_content_3519_);
                                crate::leanh::lean_dec_ref(v_content_3517_);
                                crate::leanh::lean_dec_ref(v_localinst_3432_);
                                v___x_3523_ = (crate::leanh::lean_unbox(v___x_3520_) as u8);
                                return v___x_3523_;
                            }
                        } else {
                            crate::leanh::lean_dec_ref_known(v_x_3430_, 2);
                            crate::leanh::lean_dec_ref(v_localinst_3432_);
                            crate::leanh::lean_dec_ref(v_x_3431_);
                            crate::leanh::lean_dec_ref(v_inst_3429_);
                            v___x_3524_ = 2;
                            return v___x_3524_;
                        }
                    }
                }
            }
            1 => {
                v___x_3436_ = l_Array_compareLex___redArg(v_localinst_3432_, v_a_3434_, v_b_3435_);
                crate::leanh::lean_dec_ref(v_b_3435_);
                crate::leanh::lean_dec_ref(v_a_3434_);
                if v___x_3436_ == 1 {
                    return v___x_3436_;
                } else {
                    return v___x_3436_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Doc_instOrdBlock_ord(
    mut v_i_3525_: *mut crate::leanh::LeanObject,
    mut v_b_3526_: *mut crate::leanh::LeanObject,
    mut v_inst_3527_: *mut crate::leanh::LeanObject,
    mut v_inst_3528_: *mut crate::leanh::LeanObject,
    mut v_x_3529_: *mut crate::leanh::LeanObject,
    mut v_x_3530_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_3531_: u8 = 0;
    v___x_3531_ =
        l_Lean_Doc_instOrdBlock_ord___redArg(v_inst_3527_, v_inst_3528_, v_x_3529_, v_x_3530_);
    return v___x_3531_;
}
pub unsafe fn l_Lean_Doc_instOrdBlock_ord___boxed(
    mut v_i_3532_: *mut crate::leanh::LeanObject,
    mut v_b_3533_: *mut crate::leanh::LeanObject,
    mut v_inst_3534_: *mut crate::leanh::LeanObject,
    mut v_inst_3535_: *mut crate::leanh::LeanObject,
    mut v_x_3536_: *mut crate::leanh::LeanObject,
    mut v_x_3537_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3538_: u8 = 0;
    let mut v_r_3539_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3538_ = l_Lean_Doc_instOrdBlock_ord(
        v_i_3532_,
        v_b_3533_,
        v_inst_3534_,
        v_inst_3535_,
        v_x_3536_,
        v_x_3537_,
    );
    v_r_3539_ = crate::leanh::lean_box((v_res_3538_) as usize);
    return v_r_3539_;
}
pub unsafe fn l_Lean_Doc_instOrdBlock___redArg(
    mut v_inst_3540_: *mut crate::leanh::LeanObject,
    mut v_inst_3541_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3542_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3542_ = crate::leanh::lean_alloc_closure(
        l_Lean_Doc_instOrdBlock_ord___boxed as *mut core::ffi::c_void,
        6,
        4,
    );
    crate::leanh::lean_closure_set(v___x_3542_, 0, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_3542_, 1, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_3542_, 2, v_inst_3540_);
    crate::leanh::lean_closure_set(v___x_3542_, 3, v_inst_3541_);
    return v___x_3542_;
}
pub unsafe fn l_Lean_Doc_instOrdBlock(
    mut v_i_3543_: *mut crate::leanh::LeanObject,
    mut v_b_3544_: *mut crate::leanh::LeanObject,
    mut v_inst_3545_: *mut crate::leanh::LeanObject,
    mut v_inst_3546_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3547_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3547_ = crate::leanh::lean_alloc_closure(
        l_Lean_Doc_instOrdBlock_ord___boxed as *mut core::ffi::c_void,
        6,
        4,
    );
    crate::leanh::lean_closure_set(v___x_3547_, 0, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_3547_, 1, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_3547_, 2, v_inst_3545_);
    crate::leanh::lean_closure_set(v___x_3547_, 3, v_inst_3546_);
    return v___x_3547_;
}
pub unsafe fn _init_l_Lean_Doc_instReprBlock_repr___redArg___closed__12()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3572_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3573_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3572_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_3573_ = lean_nat_to_int(v___x_3572_);
    return v___x_3573_;
}
pub unsafe fn l_Lean_Doc_instReprBlock_repr___redArg___boxed(
    mut v_inst_3598_: *mut crate::leanh::LeanObject,
    mut v_inst_3599_: *mut crate::leanh::LeanObject,
    mut v_x_3600_: *mut crate::leanh::LeanObject,
    mut v_prec_3601_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3602_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3602_ =
        l_Lean_Doc_instReprBlock_repr___redArg(v_inst_3598_, v_inst_3599_, v_x_3600_, v_prec_3601_);
    crate::leanh::lean_dec(v_prec_3601_);
    return v_res_3602_;
}
pub unsafe fn l_Lean_Doc_instReprBlock_repr___redArg(
    mut v_inst_3603_: *mut crate::leanh::LeanObject,
    mut v_inst_3604_: *mut crate::leanh::LeanObject,
    mut v_x_3605_: *mut crate::leanh::LeanObject,
    mut v_prec_3606_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_localinst_3607_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3608_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3609_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_contents_3610_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3612_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3613_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3614_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3615_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3616_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3617_: u8 = 0;
    let mut v___x_3618_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3619_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3620_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3621_: u8 = 0;
    let mut v___x_3622_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3623_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_content_3624_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3626_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3627_: u8 = 0;
    let mut v___y_3629_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3630_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3631_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3633_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3634_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3635_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3636_: u8 = 0;
    let mut v___x_3637_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3638_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3639_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3640_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3641_: u8 = 0;
    let mut v___x_3642_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3643_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3644_: u8 = 0;
    let mut v_items_3645_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3647_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3648_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3649_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3650_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3651_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3652_: u8 = 0;
    let mut v___x_3653_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3654_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3655_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3656_: u8 = 0;
    let mut v___x_3657_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3658_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_start_3659_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_items_3660_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3662_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3663_: u8 = 0;
    let mut v___y_3665_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3666_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3667_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3668_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3670_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3671_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3672_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3673_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3674_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3675_: u8 = 0;
    let mut v___x_3676_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3677_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3678_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3680_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3681_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3682_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3683_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3684_: u8 = 0;
    let mut v___x_3685_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3686_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3687_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3688_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3689_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3690_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3691_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3692_: u8 = 0;
    let mut v___x_3693_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3694_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3695_: u8 = 0;
    let mut v_items_3696_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3697_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3699_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3700_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3701_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3702_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3703_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3704_: u8 = 0;
    let mut v___x_3705_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3706_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3707_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3708_: u8 = 0;
    let mut v___x_3709_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3710_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_items_3711_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3713_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3714_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3715_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3716_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3717_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3718_: u8 = 0;
    let mut v___x_3719_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3720_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3721_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3722_: u8 = 0;
    let mut v___x_3723_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3724_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_content_3725_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3727_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3728_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3729_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3730_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3731_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3732_: u8 = 0;
    let mut v___x_3733_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3734_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3735_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3736_: u8 = 0;
    let mut v___x_3737_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3738_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_container_3739_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_content_3740_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3742_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3743_: u8 = 0;
    let mut v___y_3745_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3746_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3747_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3748_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3749_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3751_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3752_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3753_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3754_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3755_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3756_: u8 = 0;
    let mut v___x_3757_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3758_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3759_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3760_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3761_: u8 = 0;
    let mut v___x_3762_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3763_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3764_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                crate::leanh::lean_inc_ref(v_inst_3604_);
                crate::leanh::lean_inc_ref(v_inst_3603_);
                v_localinst_3607_ = crate::leanh::lean_alloc_closure(
                    l_Lean_Doc_instReprBlock_repr___redArg___boxed as *mut core::ffi::c_void,
                    4,
                    2,
                );
                crate::leanh::lean_closure_set(v_localinst_3607_, 0, v_inst_3603_);
                crate::leanh::lean_closure_set(v_localinst_3607_, 1, v_inst_3604_);
                v___x_3608_ = crate::leanh::lean_alloc_closure(
                    l_Lean_Doc_instReprInline_repr___boxed as *mut core::ffi::c_void,
                    4,
                    2,
                );
                crate::leanh::lean_closure_set(v___x_3608_, 0, crate::leanh::lean_box(0));
                crate::leanh::lean_closure_set(v___x_3608_, 1, v_inst_3603_);
                crate::leanh::lean_inc_ref(v_localinst_3607_);
                v___x_3609_ = crate::leanh::lean_alloc_closure(
                    l_Lean_Doc_instReprListItem_repr___boxed as *mut core::ffi::c_void,
                    4,
                    2,
                );
                crate::leanh::lean_closure_set(v___x_3609_, 0, crate::leanh::lean_box(0));
                crate::leanh::lean_closure_set(v___x_3609_, 1, v_localinst_3607_);
                match crate::leanh::lean_obj_tag(v_x_3605_) {
                    0 => {
                        crate::leanh::lean_dec_ref(v___x_3609_);
                        crate::leanh::lean_dec_ref(v_localinst_3607_);
                        crate::leanh::lean_dec_ref(v_inst_3604_);
                        v_contents_3610_ = crate::leanh::lean_ctor_get(v_x_3605_, 0);
                        crate::leanh::lean_inc_ref(v_contents_3610_);
                        crate::leanh::lean_dec_ref_known(v_x_3605_, 1);
                        v___x_3620_ = crate::leanh::lean_unsigned_to_nat(1024);
                        v___x_3621_ = lean_nat_dec_le(v___x_3620_, v_prec_3606_);
                        if v___x_3621_ == 0 {
                            v___x_3622_ = crate::leanh::lean_obj_once(
                                core::ptr::addr_of_mut!(
                                    l_Lean_Doc_instReprMathMode_repr___closed__4
                                ),
                                core::ptr::addr_of_mut!(
                                    l_Lean_Doc_instReprMathMode_repr___closed__4_once
                                ),
                                _init_l_Lean_Doc_instReprMathMode_repr___closed__4,
                            );
                            v___y_3612_ = v___x_3622_;
                            state = 1;
                            continue;
                        } else {
                            v___x_3623_ = crate::leanh::lean_obj_once(
                                core::ptr::addr_of_mut!(
                                    l_Lean_Doc_instReprMathMode_repr___closed__5
                                ),
                                core::ptr::addr_of_mut!(
                                    l_Lean_Doc_instReprMathMode_repr___closed__5_once
                                ),
                                _init_l_Lean_Doc_instReprMathMode_repr___closed__5,
                            );
                            v___y_3612_ = v___x_3623_;
                            state = 1;
                            continue;
                        }
                    }
                    1 => {
                        crate::leanh::lean_dec_ref(v___x_3609_);
                        crate::leanh::lean_dec_ref(v___x_3608_);
                        crate::leanh::lean_dec_ref(v_localinst_3607_);
                        crate::leanh::lean_dec_ref(v_inst_3604_);
                        v_content_3624_ = crate::leanh::lean_ctor_get(v_x_3605_, 0);
                        v_isSharedCheck_3644_ = (!crate::leanh::lean_is_exclusive(v_x_3605_)) as u8;
                        if v_isSharedCheck_3644_ == 0 {
                            v___x_3626_ = v_x_3605_;
                            v_isShared_3627_ = v_isSharedCheck_3644_;
                            state = 2;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_content_3624_);
                            crate::leanh::lean_dec(v_x_3605_);
                            v___x_3626_ = crate::leanh::lean_box(0);
                            v_isShared_3627_ = v_isSharedCheck_3644_;
                            state = 2;
                            continue;
                        }
                    }
                    2 => {
                        crate::leanh::lean_dec_ref(v___x_3608_);
                        crate::leanh::lean_dec_ref(v_localinst_3607_);
                        crate::leanh::lean_dec_ref(v_inst_3604_);
                        v_items_3645_ = crate::leanh::lean_ctor_get(v_x_3605_, 0);
                        crate::leanh::lean_inc_ref(v_items_3645_);
                        crate::leanh::lean_dec_ref_known(v_x_3605_, 1);
                        v___x_3655_ = crate::leanh::lean_unsigned_to_nat(1024);
                        v___x_3656_ = lean_nat_dec_le(v___x_3655_, v_prec_3606_);
                        if v___x_3656_ == 0 {
                            v___x_3657_ = crate::leanh::lean_obj_once(
                                core::ptr::addr_of_mut!(
                                    l_Lean_Doc_instReprMathMode_repr___closed__4
                                ),
                                core::ptr::addr_of_mut!(
                                    l_Lean_Doc_instReprMathMode_repr___closed__4_once
                                ),
                                _init_l_Lean_Doc_instReprMathMode_repr___closed__4,
                            );
                            v___y_3647_ = v___x_3657_;
                            state = 5;
                            continue;
                        } else {
                            v___x_3658_ = crate::leanh::lean_obj_once(
                                core::ptr::addr_of_mut!(
                                    l_Lean_Doc_instReprMathMode_repr___closed__5
                                ),
                                core::ptr::addr_of_mut!(
                                    l_Lean_Doc_instReprMathMode_repr___closed__5_once
                                ),
                                _init_l_Lean_Doc_instReprMathMode_repr___closed__5,
                            );
                            v___y_3647_ = v___x_3658_;
                            state = 5;
                            continue;
                        }
                    }
                    3 => {
                        crate::leanh::lean_dec_ref(v___x_3608_);
                        crate::leanh::lean_dec_ref(v_localinst_3607_);
                        crate::leanh::lean_dec_ref(v_inst_3604_);
                        v_start_3659_ = crate::leanh::lean_ctor_get(v_x_3605_, 0);
                        v_items_3660_ = crate::leanh::lean_ctor_get(v_x_3605_, 1);
                        v_isSharedCheck_3695_ = (!crate::leanh::lean_is_exclusive(v_x_3605_)) as u8;
                        if v_isSharedCheck_3695_ == 0 {
                            v___x_3662_ = v_x_3605_;
                            v_isShared_3663_ = v_isSharedCheck_3695_;
                            state = 6;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_items_3660_);
                            crate::leanh::lean_inc(v_start_3659_);
                            crate::leanh::lean_dec(v_x_3605_);
                            v___x_3662_ = crate::leanh::lean_box(0);
                            v_isShared_3663_ = v_isSharedCheck_3695_;
                            state = 6;
                            continue;
                        }
                    }
                    4 => {
                        crate::leanh::lean_dec_ref(v___x_3609_);
                        crate::leanh::lean_dec_ref(v_inst_3604_);
                        v_items_3696_ = crate::leanh::lean_ctor_get(v_x_3605_, 0);
                        crate::leanh::lean_inc_ref(v_items_3696_);
                        crate::leanh::lean_dec_ref_known(v_x_3605_, 1);
                        v___x_3697_ = crate::leanh::lean_alloc_closure(
                            l_Lean_Doc_instReprDescItem_repr___boxed as *mut core::ffi::c_void,
                            6,
                            4,
                        );
                        crate::leanh::lean_closure_set(v___x_3697_, 0, crate::leanh::lean_box(0));
                        crate::leanh::lean_closure_set(v___x_3697_, 1, crate::leanh::lean_box(0));
                        crate::leanh::lean_closure_set(v___x_3697_, 2, v___x_3608_);
                        crate::leanh::lean_closure_set(v___x_3697_, 3, v_localinst_3607_);
                        v___x_3707_ = crate::leanh::lean_unsigned_to_nat(1024);
                        v___x_3708_ = lean_nat_dec_le(v___x_3707_, v_prec_3606_);
                        if v___x_3708_ == 0 {
                            v___x_3709_ = crate::leanh::lean_obj_once(
                                core::ptr::addr_of_mut!(
                                    l_Lean_Doc_instReprMathMode_repr___closed__4
                                ),
                                core::ptr::addr_of_mut!(
                                    l_Lean_Doc_instReprMathMode_repr___closed__4_once
                                ),
                                _init_l_Lean_Doc_instReprMathMode_repr___closed__4,
                            );
                            v___y_3699_ = v___x_3709_;
                            state = 10;
                            continue;
                        } else {
                            v___x_3710_ = crate::leanh::lean_obj_once(
                                core::ptr::addr_of_mut!(
                                    l_Lean_Doc_instReprMathMode_repr___closed__5
                                ),
                                core::ptr::addr_of_mut!(
                                    l_Lean_Doc_instReprMathMode_repr___closed__5_once
                                ),
                                _init_l_Lean_Doc_instReprMathMode_repr___closed__5,
                            );
                            v___y_3699_ = v___x_3710_;
                            state = 10;
                            continue;
                        }
                    }
                    5 => {
                        crate::leanh::lean_dec_ref(v___x_3609_);
                        crate::leanh::lean_dec_ref(v___x_3608_);
                        crate::leanh::lean_dec_ref(v_inst_3604_);
                        v_items_3711_ = crate::leanh::lean_ctor_get(v_x_3605_, 0);
                        crate::leanh::lean_inc_ref(v_items_3711_);
                        crate::leanh::lean_dec_ref_known(v_x_3605_, 1);
                        v___x_3721_ = crate::leanh::lean_unsigned_to_nat(1024);
                        v___x_3722_ = lean_nat_dec_le(v___x_3721_, v_prec_3606_);
                        if v___x_3722_ == 0 {
                            v___x_3723_ = crate::leanh::lean_obj_once(
                                core::ptr::addr_of_mut!(
                                    l_Lean_Doc_instReprMathMode_repr___closed__4
                                ),
                                core::ptr::addr_of_mut!(
                                    l_Lean_Doc_instReprMathMode_repr___closed__4_once
                                ),
                                _init_l_Lean_Doc_instReprMathMode_repr___closed__4,
                            );
                            v___y_3713_ = v___x_3723_;
                            state = 11;
                            continue;
                        } else {
                            v___x_3724_ = crate::leanh::lean_obj_once(
                                core::ptr::addr_of_mut!(
                                    l_Lean_Doc_instReprMathMode_repr___closed__5
                                ),
                                core::ptr::addr_of_mut!(
                                    l_Lean_Doc_instReprMathMode_repr___closed__5_once
                                ),
                                _init_l_Lean_Doc_instReprMathMode_repr___closed__5,
                            );
                            v___y_3713_ = v___x_3724_;
                            state = 11;
                            continue;
                        }
                    }
                    6 => {
                        crate::leanh::lean_dec_ref(v___x_3609_);
                        crate::leanh::lean_dec_ref(v___x_3608_);
                        crate::leanh::lean_dec_ref(v_inst_3604_);
                        v_content_3725_ = crate::leanh::lean_ctor_get(v_x_3605_, 0);
                        crate::leanh::lean_inc_ref(v_content_3725_);
                        crate::leanh::lean_dec_ref_known(v_x_3605_, 1);
                        v___x_3735_ = crate::leanh::lean_unsigned_to_nat(1024);
                        v___x_3736_ = lean_nat_dec_le(v___x_3735_, v_prec_3606_);
                        if v___x_3736_ == 0 {
                            v___x_3737_ = crate::leanh::lean_obj_once(
                                core::ptr::addr_of_mut!(
                                    l_Lean_Doc_instReprMathMode_repr___closed__4
                                ),
                                core::ptr::addr_of_mut!(
                                    l_Lean_Doc_instReprMathMode_repr___closed__4_once
                                ),
                                _init_l_Lean_Doc_instReprMathMode_repr___closed__4,
                            );
                            v___y_3727_ = v___x_3737_;
                            state = 12;
                            continue;
                        } else {
                            v___x_3738_ = crate::leanh::lean_obj_once(
                                core::ptr::addr_of_mut!(
                                    l_Lean_Doc_instReprMathMode_repr___closed__5
                                ),
                                core::ptr::addr_of_mut!(
                                    l_Lean_Doc_instReprMathMode_repr___closed__5_once
                                ),
                                _init_l_Lean_Doc_instReprMathMode_repr___closed__5,
                            );
                            v___y_3727_ = v___x_3738_;
                            state = 12;
                            continue;
                        }
                    }
                    _ => {
                        crate::leanh::lean_dec_ref(v___x_3609_);
                        crate::leanh::lean_dec_ref(v___x_3608_);
                        v_container_3739_ = crate::leanh::lean_ctor_get(v_x_3605_, 0);
                        v_content_3740_ = crate::leanh::lean_ctor_get(v_x_3605_, 1);
                        v_isSharedCheck_3764_ = (!crate::leanh::lean_is_exclusive(v_x_3605_)) as u8;
                        if v_isSharedCheck_3764_ == 0 {
                            v___x_3742_ = v_x_3605_;
                            v_isShared_3743_ = v_isSharedCheck_3764_;
                            state = 13;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_content_3740_);
                            crate::leanh::lean_inc(v_container_3739_);
                            crate::leanh::lean_dec(v_x_3605_);
                            v___x_3742_ = crate::leanh::lean_box(0);
                            v_isShared_3743_ = v_isSharedCheck_3764_;
                            state = 13;
                            continue;
                        }
                    }
                }
            }
            1 => {
                v___x_3613_ = l_Lean_Doc_instReprBlock_repr___redArg___closed__2;
                v___x_3614_ = l_Array_repr___redArg(v___x_3608_, v_contents_3610_);
                v___x_3615_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3615_, 0, v___x_3613_);
                crate::leanh::lean_ctor_set(v___x_3615_, 1, v___x_3614_);
                crate::leanh::lean_inc(v___y_3612_);
                v___x_3616_ = crate::leanh::lean_alloc_ctor(4, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3616_, 0, v___y_3612_);
                crate::leanh::lean_ctor_set(v___x_3616_, 1, v___x_3615_);
                v___x_3617_ = 0;
                v___x_3618_ = crate::leanh::lean_alloc_ctor(6, 1, (1) as u32);
                crate::leanh::lean_ctor_set(v___x_3618_, 0, v___x_3616_);
                crate::leanh::lean_ctor_set_uint8(
                    v___x_3618_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                    v___x_3617_,
                );
                v___x_3619_ = l_Repr_addAppParen(v___x_3618_, v_prec_3606_);
                return v___x_3619_;
            }
            2 => {
                v___x_3640_ = crate::leanh::lean_unsigned_to_nat(1024);
                v___x_3641_ = lean_nat_dec_le(v___x_3640_, v_prec_3606_);
                if v___x_3641_ == 0 {
                    v___x_3642_ = crate::leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(l_Lean_Doc_instReprMathMode_repr___closed__4),
                        core::ptr::addr_of_mut!(l_Lean_Doc_instReprMathMode_repr___closed__4_once),
                        _init_l_Lean_Doc_instReprMathMode_repr___closed__4,
                    );
                    v___y_3629_ = v___x_3642_;
                    state = 3;
                    continue;
                } else {
                    v___x_3643_ = crate::leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(l_Lean_Doc_instReprMathMode_repr___closed__5),
                        core::ptr::addr_of_mut!(l_Lean_Doc_instReprMathMode_repr___closed__5_once),
                        _init_l_Lean_Doc_instReprMathMode_repr___closed__5,
                    );
                    v___y_3629_ = v___x_3643_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_3630_ = l_Lean_Doc_instReprBlock_repr___redArg___closed__5;
                v___x_3631_ = l_String_quote(v_content_3624_);
                if v_isShared_3627_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_3626_, 3);
                    crate::leanh::lean_ctor_set(v___x_3626_, 0, v___x_3631_);
                    v___x_3633_ = v___x_3626_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3639_ = crate::leanh::lean_alloc_ctor(3, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3639_, 0, v___x_3631_);
                    v___x_3633_ = v_reuseFailAlloc_3639_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_3634_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3634_, 0, v___x_3630_);
                crate::leanh::lean_ctor_set(v___x_3634_, 1, v___x_3633_);
                crate::leanh::lean_inc(v___y_3629_);
                v___x_3635_ = crate::leanh::lean_alloc_ctor(4, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3635_, 0, v___y_3629_);
                crate::leanh::lean_ctor_set(v___x_3635_, 1, v___x_3634_);
                v___x_3636_ = 0;
                v___x_3637_ = crate::leanh::lean_alloc_ctor(6, 1, (1) as u32);
                crate::leanh::lean_ctor_set(v___x_3637_, 0, v___x_3635_);
                crate::leanh::lean_ctor_set_uint8(
                    v___x_3637_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                    v___x_3636_,
                );
                v___x_3638_ = l_Repr_addAppParen(v___x_3637_, v_prec_3606_);
                return v___x_3638_;
            }
            5 => {
                v___x_3648_ = l_Lean_Doc_instReprBlock_repr___redArg___closed__8;
                v___x_3649_ = l_Array_repr___redArg(v___x_3609_, v_items_3645_);
                v___x_3650_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3650_, 0, v___x_3648_);
                crate::leanh::lean_ctor_set(v___x_3650_, 1, v___x_3649_);
                crate::leanh::lean_inc(v___y_3647_);
                v___x_3651_ = crate::leanh::lean_alloc_ctor(4, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3651_, 0, v___y_3647_);
                crate::leanh::lean_ctor_set(v___x_3651_, 1, v___x_3650_);
                v___x_3652_ = 0;
                v___x_3653_ = crate::leanh::lean_alloc_ctor(6, 1, (1) as u32);
                crate::leanh::lean_ctor_set(v___x_3653_, 0, v___x_3651_);
                crate::leanh::lean_ctor_set_uint8(
                    v___x_3653_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                    v___x_3652_,
                );
                v___x_3654_ = l_Repr_addAppParen(v___x_3653_, v_prec_3606_);
                return v___x_3654_;
            }
            6 => {
                v___x_3691_ = crate::leanh::lean_unsigned_to_nat(1024);
                v___x_3692_ = lean_nat_dec_le(v___x_3691_, v_prec_3606_);
                if v___x_3692_ == 0 {
                    v___x_3693_ = crate::leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(l_Lean_Doc_instReprMathMode_repr___closed__4),
                        core::ptr::addr_of_mut!(l_Lean_Doc_instReprMathMode_repr___closed__4_once),
                        _init_l_Lean_Doc_instReprMathMode_repr___closed__4,
                    );
                    v___y_3680_ = v___x_3693_;
                    state = 9;
                    continue;
                } else {
                    v___x_3694_ = crate::leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(l_Lean_Doc_instReprMathMode_repr___closed__5),
                        core::ptr::addr_of_mut!(l_Lean_Doc_instReprMathMode_repr___closed__5_once),
                        _init_l_Lean_Doc_instReprMathMode_repr___closed__5,
                    );
                    v___y_3680_ = v___x_3694_;
                    state = 9;
                    continue;
                }
            }
            7 => {
                crate::leanh::lean_inc(v___y_3665_);
                if v_isShared_3663_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_3662_, 5);
                    crate::leanh::lean_ctor_set(v___x_3662_, 1, v___y_3668_);
                    crate::leanh::lean_ctor_set(v___x_3662_, 0, v___y_3665_);
                    v___x_3670_ = v___x_3662_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_3678_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3678_, 0, v___y_3665_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3678_, 1, v___y_3668_);
                    v___x_3670_ = v_reuseFailAlloc_3678_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                crate::leanh::lean_inc(v___y_3666_);
                v___x_3671_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3671_, 0, v___x_3670_);
                crate::leanh::lean_ctor_set(v___x_3671_, 1, v___y_3666_);
                v___x_3672_ = l_Array_repr___redArg(v___x_3609_, v_items_3660_);
                v___x_3673_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3673_, 0, v___x_3671_);
                crate::leanh::lean_ctor_set(v___x_3673_, 1, v___x_3672_);
                crate::leanh::lean_inc(v___y_3667_);
                v___x_3674_ = crate::leanh::lean_alloc_ctor(4, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3674_, 0, v___y_3667_);
                crate::leanh::lean_ctor_set(v___x_3674_, 1, v___x_3673_);
                v___x_3675_ = 0;
                v___x_3676_ = crate::leanh::lean_alloc_ctor(6, 1, (1) as u32);
                crate::leanh::lean_ctor_set(v___x_3676_, 0, v___x_3674_);
                crate::leanh::lean_ctor_set_uint8(
                    v___x_3676_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                    v___x_3675_,
                );
                v___x_3677_ = l_Repr_addAppParen(v___x_3676_, v_prec_3606_);
                return v___x_3677_;
            }
            9 => {
                v___x_3681_ = crate::leanh::lean_box(1);
                v___x_3682_ = l_Lean_Doc_instReprBlock_repr___redArg___closed__11;
                v___x_3683_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lean_Doc_instReprBlock_repr___redArg___closed__12),
                    core::ptr::addr_of_mut!(
                        l_Lean_Doc_instReprBlock_repr___redArg___closed__12_once
                    ),
                    _init_l_Lean_Doc_instReprBlock_repr___redArg___closed__12,
                );
                v___x_3684_ = lean_int_dec_lt(v_start_3659_, v___x_3683_);
                if v___x_3684_ == 0 {
                    v___x_3685_ = l_Int_repr(v_start_3659_);
                    crate::leanh::lean_dec(v_start_3659_);
                    v___x_3686_ = crate::leanh::lean_alloc_ctor(3, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_3686_, 0, v___x_3685_);
                    v___y_3665_ = v___x_3682_;
                    v___y_3666_ = v___x_3681_;
                    v___y_3667_ = v___y_3680_;
                    v___y_3668_ = v___x_3686_;
                    state = 7;
                    continue;
                } else {
                    v___x_3687_ = crate::leanh::lean_unsigned_to_nat(1024);
                    v___x_3688_ = l_Int_repr(v_start_3659_);
                    crate::leanh::lean_dec(v_start_3659_);
                    v___x_3689_ = crate::leanh::lean_alloc_ctor(3, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_3689_, 0, v___x_3688_);
                    v___x_3690_ = l_Repr_addAppParen(v___x_3689_, v___x_3687_);
                    v___y_3665_ = v___x_3682_;
                    v___y_3666_ = v___x_3681_;
                    v___y_3667_ = v___y_3680_;
                    v___y_3668_ = v___x_3690_;
                    state = 7;
                    continue;
                }
            }
            10 => {
                v___x_3700_ = l_Lean_Doc_instReprBlock_repr___redArg___closed__15;
                v___x_3701_ = l_Array_repr___redArg(v___x_3697_, v_items_3696_);
                v___x_3702_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3702_, 0, v___x_3700_);
                crate::leanh::lean_ctor_set(v___x_3702_, 1, v___x_3701_);
                crate::leanh::lean_inc(v___y_3699_);
                v___x_3703_ = crate::leanh::lean_alloc_ctor(4, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3703_, 0, v___y_3699_);
                crate::leanh::lean_ctor_set(v___x_3703_, 1, v___x_3702_);
                v___x_3704_ = 0;
                v___x_3705_ = crate::leanh::lean_alloc_ctor(6, 1, (1) as u32);
                crate::leanh::lean_ctor_set(v___x_3705_, 0, v___x_3703_);
                crate::leanh::lean_ctor_set_uint8(
                    v___x_3705_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                    v___x_3704_,
                );
                v___x_3706_ = l_Repr_addAppParen(v___x_3705_, v_prec_3606_);
                return v___x_3706_;
            }
            11 => {
                v___x_3714_ = l_Lean_Doc_instReprBlock_repr___redArg___closed__18;
                v___x_3715_ = l_Array_repr___redArg(v_localinst_3607_, v_items_3711_);
                v___x_3716_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3716_, 0, v___x_3714_);
                crate::leanh::lean_ctor_set(v___x_3716_, 1, v___x_3715_);
                crate::leanh::lean_inc(v___y_3713_);
                v___x_3717_ = crate::leanh::lean_alloc_ctor(4, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3717_, 0, v___y_3713_);
                crate::leanh::lean_ctor_set(v___x_3717_, 1, v___x_3716_);
                v___x_3718_ = 0;
                v___x_3719_ = crate::leanh::lean_alloc_ctor(6, 1, (1) as u32);
                crate::leanh::lean_ctor_set(v___x_3719_, 0, v___x_3717_);
                crate::leanh::lean_ctor_set_uint8(
                    v___x_3719_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                    v___x_3718_,
                );
                v___x_3720_ = l_Repr_addAppParen(v___x_3719_, v_prec_3606_);
                return v___x_3720_;
            }
            12 => {
                v___x_3728_ = l_Lean_Doc_instReprBlock_repr___redArg___closed__21;
                v___x_3729_ = l_Array_repr___redArg(v_localinst_3607_, v_content_3725_);
                v___x_3730_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3730_, 0, v___x_3728_);
                crate::leanh::lean_ctor_set(v___x_3730_, 1, v___x_3729_);
                crate::leanh::lean_inc(v___y_3727_);
                v___x_3731_ = crate::leanh::lean_alloc_ctor(4, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3731_, 0, v___y_3727_);
                crate::leanh::lean_ctor_set(v___x_3731_, 1, v___x_3730_);
                v___x_3732_ = 0;
                v___x_3733_ = crate::leanh::lean_alloc_ctor(6, 1, (1) as u32);
                crate::leanh::lean_ctor_set(v___x_3733_, 0, v___x_3731_);
                crate::leanh::lean_ctor_set_uint8(
                    v___x_3733_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                    v___x_3732_,
                );
                v___x_3734_ = l_Repr_addAppParen(v___x_3733_, v_prec_3606_);
                return v___x_3734_;
            }
            13 => {
                v___x_3760_ = crate::leanh::lean_unsigned_to_nat(1024);
                v___x_3761_ = lean_nat_dec_le(v___x_3760_, v_prec_3606_);
                if v___x_3761_ == 0 {
                    v___x_3762_ = crate::leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(l_Lean_Doc_instReprMathMode_repr___closed__4),
                        core::ptr::addr_of_mut!(l_Lean_Doc_instReprMathMode_repr___closed__4_once),
                        _init_l_Lean_Doc_instReprMathMode_repr___closed__4,
                    );
                    v___y_3745_ = v___x_3762_;
                    state = 14;
                    continue;
                } else {
                    v___x_3763_ = crate::leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(l_Lean_Doc_instReprMathMode_repr___closed__5),
                        core::ptr::addr_of_mut!(l_Lean_Doc_instReprMathMode_repr___closed__5_once),
                        _init_l_Lean_Doc_instReprMathMode_repr___closed__5,
                    );
                    v___y_3745_ = v___x_3763_;
                    state = 14;
                    continue;
                }
            }
            14 => {
                v___x_3746_ = crate::leanh::lean_box(1);
                v___x_3747_ = l_Lean_Doc_instReprBlock_repr___redArg___closed__24;
                v___x_3748_ = crate::leanh::lean_unsigned_to_nat(1024);
                v___x_3749_ =
                    crate::leanh::lean_apply_2(v_inst_3604_, v_container_3739_, v___x_3748_);
                if v_isShared_3743_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_3742_, 5);
                    crate::leanh::lean_ctor_set(v___x_3742_, 1, v___x_3749_);
                    crate::leanh::lean_ctor_set(v___x_3742_, 0, v___x_3747_);
                    v___x_3751_ = v___x_3742_;
                    state = 15;
                    continue;
                } else {
                    v_reuseFailAlloc_3759_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3759_, 0, v___x_3747_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3759_, 1, v___x_3749_);
                    v___x_3751_ = v_reuseFailAlloc_3759_;
                    state = 15;
                    continue;
                }
            }
            15 => {
                v___x_3752_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3752_, 0, v___x_3751_);
                crate::leanh::lean_ctor_set(v___x_3752_, 1, v___x_3746_);
                v___x_3753_ = l_Array_repr___redArg(v_localinst_3607_, v_content_3740_);
                v___x_3754_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3754_, 0, v___x_3752_);
                crate::leanh::lean_ctor_set(v___x_3754_, 1, v___x_3753_);
                crate::leanh::lean_inc(v___y_3745_);
                v___x_3755_ = crate::leanh::lean_alloc_ctor(4, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3755_, 0, v___y_3745_);
                crate::leanh::lean_ctor_set(v___x_3755_, 1, v___x_3754_);
                v___x_3756_ = 0;
                v___x_3757_ = crate::leanh::lean_alloc_ctor(6, 1, (1) as u32);
                crate::leanh::lean_ctor_set(v___x_3757_, 0, v___x_3755_);
                crate::leanh::lean_ctor_set_uint8(
                    v___x_3757_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                    v___x_3756_,
                );
                v___x_3758_ = l_Repr_addAppParen(v___x_3757_, v_prec_3606_);
                return v___x_3758_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Doc_instReprBlock_repr(
    mut v_i_3765_: *mut crate::leanh::LeanObject,
    mut v_b_3766_: *mut crate::leanh::LeanObject,
    mut v_inst_3767_: *mut crate::leanh::LeanObject,
    mut v_inst_3768_: *mut crate::leanh::LeanObject,
    mut v_x_3769_: *mut crate::leanh::LeanObject,
    mut v_prec_3770_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3771_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3771_ =
        l_Lean_Doc_instReprBlock_repr___redArg(v_inst_3767_, v_inst_3768_, v_x_3769_, v_prec_3770_);
    return v___x_3771_;
}
pub unsafe fn l_Lean_Doc_instReprBlock_repr___boxed(
    mut v_i_3772_: *mut crate::leanh::LeanObject,
    mut v_b_3773_: *mut crate::leanh::LeanObject,
    mut v_inst_3774_: *mut crate::leanh::LeanObject,
    mut v_inst_3775_: *mut crate::leanh::LeanObject,
    mut v_x_3776_: *mut crate::leanh::LeanObject,
    mut v_prec_3777_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3778_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3778_ = l_Lean_Doc_instReprBlock_repr(
        v_i_3772_,
        v_b_3773_,
        v_inst_3774_,
        v_inst_3775_,
        v_x_3776_,
        v_prec_3777_,
    );
    crate::leanh::lean_dec(v_prec_3777_);
    return v_res_3778_;
}
pub unsafe fn l_Lean_Doc_instReprBlock___redArg(
    mut v_inst_3779_: *mut crate::leanh::LeanObject,
    mut v_inst_3780_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3781_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3781_ = crate::leanh::lean_alloc_closure(
        l_Lean_Doc_instReprBlock_repr___boxed as *mut core::ffi::c_void,
        6,
        4,
    );
    crate::leanh::lean_closure_set(v___x_3781_, 0, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_3781_, 1, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_3781_, 2, v_inst_3779_);
    crate::leanh::lean_closure_set(v___x_3781_, 3, v_inst_3780_);
    return v___x_3781_;
}
pub unsafe fn l_Lean_Doc_instReprBlock(
    mut v_i_3782_: *mut crate::leanh::LeanObject,
    mut v_b_3783_: *mut crate::leanh::LeanObject,
    mut v_inst_3784_: *mut crate::leanh::LeanObject,
    mut v_inst_3785_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3786_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3786_ = crate::leanh::lean_alloc_closure(
        l_Lean_Doc_instReprBlock_repr___boxed as *mut core::ffi::c_void,
        6,
        4,
    );
    crate::leanh::lean_closure_set(v___x_3786_, 0, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_3786_, 1, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_3786_, 2, v_inst_3784_);
    crate::leanh::lean_closure_set(v___x_3786_, 3, v_inst_3785_);
    return v___x_3786_;
}
pub unsafe fn l_Lean_Doc_instInhabitedBlock_default(
    mut v_i_3791_: *mut crate::leanh::LeanObject,
    mut v_b_3792_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3793_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3793_ = l_Lean_Doc_instInhabitedBlock_default___closed__1;
    return v___x_3793_;
}
pub unsafe fn _init_l_Lean_Doc_instInhabitedBlock___closed__0() -> *mut crate::leanh::LeanObject {
    let mut v___x_3794_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3794_ =
        l_Lean_Doc_instInhabitedBlock_default(crate::leanh::lean_box(0), crate::leanh::lean_box(0));
    return v___x_3794_;
}
pub unsafe fn l_Lean_Doc_instInhabitedBlock(
    mut v_a_3795_: *mut crate::leanh::LeanObject,
    mut v_a_3796_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3797_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3797_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Doc_instInhabitedBlock___closed__0),
        core::ptr::addr_of_mut!(l_Lean_Doc_instInhabitedBlock___closed__0_once),
        _init_l_Lean_Doc_instInhabitedBlock___closed__0,
    );
    return v___x_3797_;
}
pub unsafe fn l_Lean_Doc_Block_empty(
    mut v_i_3802_: *mut crate::leanh::LeanObject,
    mut v_b_3803_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3804_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3804_ = l_Lean_Doc_Block_empty___closed__1;
    return v___x_3804_;
}
pub unsafe fn l_Lean_Doc_Block_cast___redArg(
    mut v_x_3805_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc_ref(v_x_3805_);
    return v_x_3805_;
}
pub unsafe fn l_Lean_Doc_Block_cast___redArg___boxed(
    mut v_x_3806_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3807_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3807_ = l_Lean_Doc_Block_cast___redArg(v_x_3806_);
    crate::leanh::lean_dec_ref(v_x_3806_);
    return v_res_3807_;
}
pub unsafe fn l_Lean_Doc_Block_cast(
    mut v_i_3808_: *mut crate::leanh::LeanObject,
    mut v_i_x27_3809_: *mut crate::leanh::LeanObject,
    mut v_b_3810_: *mut crate::leanh::LeanObject,
    mut v_b_x27_3811_: *mut crate::leanh::LeanObject,
    mut v_inlines__eq_3812_: *mut crate::leanh::LeanObject,
    mut v_blocks__eq_3813_: *mut crate::leanh::LeanObject,
    mut v_x_3814_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc_ref(v_x_3814_);
    return v_x_3814_;
}
pub unsafe fn l_Lean_Doc_Block_cast___boxed(
    mut v_i_3815_: *mut crate::leanh::LeanObject,
    mut v_i_x27_3816_: *mut crate::leanh::LeanObject,
    mut v_b_3817_: *mut crate::leanh::LeanObject,
    mut v_b_x27_3818_: *mut crate::leanh::LeanObject,
    mut v_inlines__eq_3819_: *mut crate::leanh::LeanObject,
    mut v_blocks__eq_3820_: *mut crate::leanh::LeanObject,
    mut v_x_3821_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3822_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3822_ = l_Lean_Doc_Block_cast(
        v_i_3815_,
        v_i_x27_3816_,
        v_b_3817_,
        v_b_x27_3818_,
        v_inlines__eq_3819_,
        v_blocks__eq_3820_,
        v_x_3821_,
    );
    crate::leanh::lean_dec_ref(v_x_3821_);
    return v_res_3822_;
}
pub unsafe fn l_Lean_Doc_instBEqPart_beq___redArg___boxed(
    mut v_inst_3823_: *mut crate::leanh::LeanObject,
    mut v_inst_3824_: *mut crate::leanh::LeanObject,
    mut v_inst_3825_: *mut crate::leanh::LeanObject,
    mut v_x_3826_: *mut crate::leanh::LeanObject,
    mut v_x_3827_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3828_: u8 = 0;
    let mut v_r_3829_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3828_ = l_Lean_Doc_instBEqPart_beq___redArg(
        v_inst_3823_,
        v_inst_3824_,
        v_inst_3825_,
        v_x_3826_,
        v_x_3827_,
    );
    v_r_3829_ = crate::leanh::lean_box((v_res_3828_) as usize);
    return v_r_3829_;
}
pub unsafe fn l_Lean_Doc_instBEqPart_beq___redArg(
    mut v_inst_3830_: *mut crate::leanh::LeanObject,
    mut v_inst_3831_: *mut crate::leanh::LeanObject,
    mut v_inst_3832_: *mut crate::leanh::LeanObject,
    mut v_x_3833_: *mut crate::leanh::LeanObject,
    mut v_x_3834_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v_title_3835_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_titleString_3836_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_metadata_3837_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_content_3838_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_subParts_3839_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_title_3840_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_titleString_3841_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_metadata_3842_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_content_3843_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_subParts_3844_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3845_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3846_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3847_: u8 = 0;
    v_title_3835_ = crate::leanh::lean_ctor_get(v_x_3833_, 0);
    crate::leanh::lean_inc_ref(v_title_3835_);
    v_titleString_3836_ = crate::leanh::lean_ctor_get(v_x_3833_, 1);
    crate::leanh::lean_inc_ref(v_titleString_3836_);
    v_metadata_3837_ = crate::leanh::lean_ctor_get(v_x_3833_, 2);
    crate::leanh::lean_inc(v_metadata_3837_);
    v_content_3838_ = crate::leanh::lean_ctor_get(v_x_3833_, 3);
    crate::leanh::lean_inc_ref(v_content_3838_);
    v_subParts_3839_ = crate::leanh::lean_ctor_get(v_x_3833_, 4);
    crate::leanh::lean_inc_ref(v_subParts_3839_);
    crate::leanh::lean_dec_ref(v_x_3833_);
    v_title_3840_ = crate::leanh::lean_ctor_get(v_x_3834_, 0);
    crate::leanh::lean_inc_ref(v_title_3840_);
    v_titleString_3841_ = crate::leanh::lean_ctor_get(v_x_3834_, 1);
    crate::leanh::lean_inc_ref(v_titleString_3841_);
    v_metadata_3842_ = crate::leanh::lean_ctor_get(v_x_3834_, 2);
    crate::leanh::lean_inc(v_metadata_3842_);
    v_content_3843_ = crate::leanh::lean_ctor_get(v_x_3834_, 3);
    crate::leanh::lean_inc_ref(v_content_3843_);
    v_subParts_3844_ = crate::leanh::lean_ctor_get(v_x_3834_, 4);
    crate::leanh::lean_inc_ref(v_subParts_3844_);
    crate::leanh::lean_dec_ref(v_x_3834_);
    v___x_3845_ = lean_array_get_size(v_title_3835_);
    v___x_3846_ = lean_array_get_size(v_title_3840_);
    v___x_3847_ = lean_nat_dec_eq(v___x_3845_, v___x_3846_);
    if v___x_3847_ == 0 {
        crate::leanh::lean_dec_ref(v_subParts_3844_);
        crate::leanh::lean_dec_ref(v_content_3843_);
        crate::leanh::lean_dec(v_metadata_3842_);
        crate::leanh::lean_dec_ref(v_titleString_3841_);
        crate::leanh::lean_dec_ref(v_title_3840_);
        crate::leanh::lean_dec_ref(v_subParts_3839_);
        crate::leanh::lean_dec_ref(v_content_3838_);
        crate::leanh::lean_dec(v_metadata_3837_);
        crate::leanh::lean_dec_ref(v_titleString_3836_);
        crate::leanh::lean_dec_ref(v_title_3835_);
        crate::leanh::lean_dec_ref(v_inst_3832_);
        crate::leanh::lean_dec_ref(v_inst_3831_);
        crate::leanh::lean_dec_ref(v_inst_3830_);
        return v___x_3847_;
    } else {
        let mut v___x_3848_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3849_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3850_: u8 = 0;
        crate::leanh::lean_inc_ref(v_inst_3832_);
        crate::leanh::lean_inc_ref(v_inst_3831_);
        crate::leanh::lean_inc_ref_n(v_inst_3830_, 2);
        v___x_3848_ = crate::leanh::lean_alloc_closure(
            l_Lean_Doc_instBEqPart_beq___redArg___boxed as *mut core::ffi::c_void,
            5,
            3,
        );
        crate::leanh::lean_closure_set(v___x_3848_, 0, v_inst_3830_);
        crate::leanh::lean_closure_set(v___x_3848_, 1, v_inst_3831_);
        crate::leanh::lean_closure_set(v___x_3848_, 2, v_inst_3832_);
        v___x_3849_ = crate::leanh::lean_alloc_closure(
            l_Lean_Doc_instBEqInline_beq___boxed as *mut core::ffi::c_void,
            4,
            2,
        );
        crate::leanh::lean_closure_set(v___x_3849_, 0, crate::leanh::lean_box(0));
        crate::leanh::lean_closure_set(v___x_3849_, 1, v_inst_3830_);
        v___x_3850_ =
            l_Array_isEqvAux___redArg(v_title_3835_, v_title_3840_, v___x_3849_, v___x_3845_);
        crate::leanh::lean_dec_ref(v_title_3840_);
        crate::leanh::lean_dec_ref(v_title_3835_);
        if v___x_3850_ == 0 {
            crate::leanh::lean_dec_ref(v___x_3848_);
            crate::leanh::lean_dec_ref(v_subParts_3844_);
            crate::leanh::lean_dec_ref(v_content_3843_);
            crate::leanh::lean_dec(v_metadata_3842_);
            crate::leanh::lean_dec_ref(v_titleString_3841_);
            crate::leanh::lean_dec_ref(v_subParts_3839_);
            crate::leanh::lean_dec_ref(v_content_3838_);
            crate::leanh::lean_dec(v_metadata_3837_);
            crate::leanh::lean_dec_ref(v_titleString_3836_);
            crate::leanh::lean_dec_ref(v_inst_3832_);
            crate::leanh::lean_dec_ref(v_inst_3831_);
            crate::leanh::lean_dec_ref(v_inst_3830_);
            return v___x_3850_;
        } else {
            let mut v___x_3851_: u8 = 0;
            v___x_3851_ = lean_string_dec_eq(v_titleString_3836_, v_titleString_3841_);
            crate::leanh::lean_dec_ref(v_titleString_3841_);
            crate::leanh::lean_dec_ref(v_titleString_3836_);
            if v___x_3851_ == 0 {
                crate::leanh::lean_dec_ref(v___x_3848_);
                crate::leanh::lean_dec_ref(v_subParts_3844_);
                crate::leanh::lean_dec_ref(v_content_3843_);
                crate::leanh::lean_dec(v_metadata_3842_);
                crate::leanh::lean_dec_ref(v_subParts_3839_);
                crate::leanh::lean_dec_ref(v_content_3838_);
                crate::leanh::lean_dec(v_metadata_3837_);
                crate::leanh::lean_dec_ref(v_inst_3832_);
                crate::leanh::lean_dec_ref(v_inst_3831_);
                crate::leanh::lean_dec_ref(v_inst_3830_);
                return v___x_3851_;
            } else {
                let mut v___x_3852_: u8 = 0;
                v___x_3852_ =
                    l_Option_instBEq_beq___redArg(v_inst_3832_, v_metadata_3837_, v_metadata_3842_);
                if v___x_3852_ == 0 {
                    crate::leanh::lean_dec_ref(v___x_3848_);
                    crate::leanh::lean_dec_ref(v_subParts_3844_);
                    crate::leanh::lean_dec_ref(v_content_3843_);
                    crate::leanh::lean_dec_ref(v_subParts_3839_);
                    crate::leanh::lean_dec_ref(v_content_3838_);
                    crate::leanh::lean_dec_ref(v_inst_3831_);
                    crate::leanh::lean_dec_ref(v_inst_3830_);
                    return v___x_3852_;
                } else {
                    let mut v___x_3853_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                    let mut v___x_3854_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                    let mut v___x_3855_: u8 = 0;
                    v___x_3853_ = lean_array_get_size(v_content_3838_);
                    v___x_3854_ = lean_array_get_size(v_content_3843_);
                    v___x_3855_ = lean_nat_dec_eq(v___x_3853_, v___x_3854_);
                    if v___x_3855_ == 0 {
                        crate::leanh::lean_dec_ref(v___x_3848_);
                        crate::leanh::lean_dec_ref(v_subParts_3844_);
                        crate::leanh::lean_dec_ref(v_content_3843_);
                        crate::leanh::lean_dec_ref(v_subParts_3839_);
                        crate::leanh::lean_dec_ref(v_content_3838_);
                        crate::leanh::lean_dec_ref(v_inst_3831_);
                        crate::leanh::lean_dec_ref(v_inst_3830_);
                        return v___x_3855_;
                    } else {
                        let mut v___x_3856_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                        let mut v___x_3857_: u8 = 0;
                        v___x_3856_ = crate::leanh::lean_alloc_closure(
                            l_Lean_Doc_instBEqBlock_beq___boxed as *mut core::ffi::c_void,
                            6,
                            4,
                        );
                        crate::leanh::lean_closure_set(v___x_3856_, 0, crate::leanh::lean_box(0));
                        crate::leanh::lean_closure_set(v___x_3856_, 1, crate::leanh::lean_box(0));
                        crate::leanh::lean_closure_set(v___x_3856_, 2, v_inst_3830_);
                        crate::leanh::lean_closure_set(v___x_3856_, 3, v_inst_3831_);
                        v___x_3857_ = l_Array_isEqvAux___redArg(
                            v_content_3838_,
                            v_content_3843_,
                            v___x_3856_,
                            v___x_3853_,
                        );
                        crate::leanh::lean_dec_ref(v_content_3843_);
                        crate::leanh::lean_dec_ref(v_content_3838_);
                        if v___x_3857_ == 0 {
                            crate::leanh::lean_dec_ref(v___x_3848_);
                            crate::leanh::lean_dec_ref(v_subParts_3844_);
                            crate::leanh::lean_dec_ref(v_subParts_3839_);
                            return v___x_3857_;
                        } else {
                            let mut v___x_3858_: *mut crate::leanh::LeanObject =
                                core::ptr::null_mut();
                            let mut v___x_3859_: *mut crate::leanh::LeanObject =
                                core::ptr::null_mut();
                            let mut v___x_3860_: u8 = 0;
                            v___x_3858_ = lean_array_get_size(v_subParts_3839_);
                            v___x_3859_ = lean_array_get_size(v_subParts_3844_);
                            v___x_3860_ = lean_nat_dec_eq(v___x_3858_, v___x_3859_);
                            if v___x_3860_ == 0 {
                                crate::leanh::lean_dec_ref(v___x_3848_);
                                crate::leanh::lean_dec_ref(v_subParts_3844_);
                                crate::leanh::lean_dec_ref(v_subParts_3839_);
                                return v___x_3860_;
                            } else {
                                let mut v___x_3861_: u8 = 0;
                                v___x_3861_ = l_Array_isEqvAux___redArg(
                                    v_subParts_3839_,
                                    v_subParts_3844_,
                                    v___x_3848_,
                                    v___x_3858_,
                                );
                                crate::leanh::lean_dec_ref(v_subParts_3844_);
                                crate::leanh::lean_dec_ref(v_subParts_3839_);
                                return v___x_3861_;
                            }
                        }
                    }
                }
            }
        }
    }
}
pub unsafe fn l_Lean_Doc_instBEqPart_beq(
    mut v_i_3862_: *mut crate::leanh::LeanObject,
    mut v_b_3863_: *mut crate::leanh::LeanObject,
    mut v_p_3864_: *mut crate::leanh::LeanObject,
    mut v_inst_3865_: *mut crate::leanh::LeanObject,
    mut v_inst_3866_: *mut crate::leanh::LeanObject,
    mut v_inst_3867_: *mut crate::leanh::LeanObject,
    mut v_x_3868_: *mut crate::leanh::LeanObject,
    mut v_x_3869_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_3870_: u8 = 0;
    v___x_3870_ = l_Lean_Doc_instBEqPart_beq___redArg(
        v_inst_3865_,
        v_inst_3866_,
        v_inst_3867_,
        v_x_3868_,
        v_x_3869_,
    );
    return v___x_3870_;
}
pub unsafe fn l_Lean_Doc_instBEqPart_beq___boxed(
    mut v_i_3871_: *mut crate::leanh::LeanObject,
    mut v_b_3872_: *mut crate::leanh::LeanObject,
    mut v_p_3873_: *mut crate::leanh::LeanObject,
    mut v_inst_3874_: *mut crate::leanh::LeanObject,
    mut v_inst_3875_: *mut crate::leanh::LeanObject,
    mut v_inst_3876_: *mut crate::leanh::LeanObject,
    mut v_x_3877_: *mut crate::leanh::LeanObject,
    mut v_x_3878_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3879_: u8 = 0;
    let mut v_r_3880_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3879_ = l_Lean_Doc_instBEqPart_beq(
        v_i_3871_,
        v_b_3872_,
        v_p_3873_,
        v_inst_3874_,
        v_inst_3875_,
        v_inst_3876_,
        v_x_3877_,
        v_x_3878_,
    );
    v_r_3880_ = crate::leanh::lean_box((v_res_3879_) as usize);
    return v_r_3880_;
}
pub unsafe fn l_Lean_Doc_instBEqPart___redArg(
    mut v_inst_3881_: *mut crate::leanh::LeanObject,
    mut v_inst_3882_: *mut crate::leanh::LeanObject,
    mut v_inst_3883_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3884_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3884_ = crate::leanh::lean_alloc_closure(
        l_Lean_Doc_instBEqPart_beq___boxed as *mut core::ffi::c_void,
        8,
        6,
    );
    crate::leanh::lean_closure_set(v___x_3884_, 0, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_3884_, 1, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_3884_, 2, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_3884_, 3, v_inst_3881_);
    crate::leanh::lean_closure_set(v___x_3884_, 4, v_inst_3882_);
    crate::leanh::lean_closure_set(v___x_3884_, 5, v_inst_3883_);
    return v___x_3884_;
}
pub unsafe fn l_Lean_Doc_instBEqPart(
    mut v_i_3885_: *mut crate::leanh::LeanObject,
    mut v_b_3886_: *mut crate::leanh::LeanObject,
    mut v_p_3887_: *mut crate::leanh::LeanObject,
    mut v_inst_3888_: *mut crate::leanh::LeanObject,
    mut v_inst_3889_: *mut crate::leanh::LeanObject,
    mut v_inst_3890_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3891_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3891_ = crate::leanh::lean_alloc_closure(
        l_Lean_Doc_instBEqPart_beq___boxed as *mut core::ffi::c_void,
        8,
        6,
    );
    crate::leanh::lean_closure_set(v___x_3891_, 0, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_3891_, 1, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_3891_, 2, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_3891_, 3, v_inst_3888_);
    crate::leanh::lean_closure_set(v___x_3891_, 4, v_inst_3889_);
    crate::leanh::lean_closure_set(v___x_3891_, 5, v_inst_3890_);
    return v___x_3891_;
}
pub unsafe fn l_Lean_Doc_instOrdPart_ord___redArg___boxed(
    mut v_inst_3892_: *mut crate::leanh::LeanObject,
    mut v_inst_3893_: *mut crate::leanh::LeanObject,
    mut v_inst_3894_: *mut crate::leanh::LeanObject,
    mut v_x_3895_: *mut crate::leanh::LeanObject,
    mut v_x_3896_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3897_: u8 = 0;
    let mut v_r_3898_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3897_ = l_Lean_Doc_instOrdPart_ord___redArg(
        v_inst_3892_,
        v_inst_3893_,
        v_inst_3894_,
        v_x_3895_,
        v_x_3896_,
    );
    v_r_3898_ = crate::leanh::lean_box((v_res_3897_) as usize);
    return v_r_3898_;
}
pub unsafe fn l_Lean_Doc_instOrdPart_ord___redArg(
    mut v_inst_3899_: *mut crate::leanh::LeanObject,
    mut v_inst_3900_: *mut crate::leanh::LeanObject,
    mut v_inst_3901_: *mut crate::leanh::LeanObject,
    mut v_x_3902_: *mut crate::leanh::LeanObject,
    mut v_x_3903_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v_title_3904_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_titleString_3905_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_metadata_3906_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_content_3907_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_subParts_3908_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_title_3909_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_titleString_3910_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_metadata_3911_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_content_3912_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_subParts_3913_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3914_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3916_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3917_: u8 = 0;
    let mut v___x_3918_: u8 = 0;
    let mut v___x_3919_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3920_: u8 = 0;
    let mut v___x_3921_: u8 = 0;
    let mut v___x_3922_: u8 = 0;
    let mut v___x_3923_: u8 = 0;
    let mut v_val_3924_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_3925_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3926_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3927_: u8 = 0;
    let mut v___x_3928_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_title_3904_ = crate::leanh::lean_ctor_get(v_x_3902_, 0);
                crate::leanh::lean_inc_ref(v_title_3904_);
                v_titleString_3905_ = crate::leanh::lean_ctor_get(v_x_3902_, 1);
                crate::leanh::lean_inc_ref(v_titleString_3905_);
                v_metadata_3906_ = crate::leanh::lean_ctor_get(v_x_3902_, 2);
                crate::leanh::lean_inc(v_metadata_3906_);
                v_content_3907_ = crate::leanh::lean_ctor_get(v_x_3902_, 3);
                crate::leanh::lean_inc_ref(v_content_3907_);
                v_subParts_3908_ = crate::leanh::lean_ctor_get(v_x_3902_, 4);
                crate::leanh::lean_inc_ref(v_subParts_3908_);
                crate::leanh::lean_dec_ref(v_x_3902_);
                v_title_3909_ = crate::leanh::lean_ctor_get(v_x_3903_, 0);
                crate::leanh::lean_inc_ref(v_title_3909_);
                v_titleString_3910_ = crate::leanh::lean_ctor_get(v_x_3903_, 1);
                crate::leanh::lean_inc_ref(v_titleString_3910_);
                v_metadata_3911_ = crate::leanh::lean_ctor_get(v_x_3903_, 2);
                crate::leanh::lean_inc(v_metadata_3911_);
                v_content_3912_ = crate::leanh::lean_ctor_get(v_x_3903_, 3);
                crate::leanh::lean_inc_ref(v_content_3912_);
                v_subParts_3913_ = crate::leanh::lean_ctor_get(v_x_3903_, 4);
                crate::leanh::lean_inc_ref(v_subParts_3913_);
                crate::leanh::lean_dec_ref(v_x_3903_);
                crate::leanh::lean_inc_ref(v_inst_3901_);
                crate::leanh::lean_inc_ref(v_inst_3900_);
                crate::leanh::lean_inc_ref_n(v_inst_3899_, 2);
                v___x_3914_ = crate::leanh::lean_alloc_closure(
                    l_Lean_Doc_instOrdPart_ord___redArg___boxed as *mut core::ffi::c_void,
                    5,
                    3,
                );
                crate::leanh::lean_closure_set(v___x_3914_, 0, v_inst_3899_);
                crate::leanh::lean_closure_set(v___x_3914_, 1, v_inst_3900_);
                crate::leanh::lean_closure_set(v___x_3914_, 2, v_inst_3901_);
                v___x_3919_ = crate::leanh::lean_alloc_closure(
                    l_Lean_Doc_instOrdInline_ord___boxed as *mut core::ffi::c_void,
                    4,
                    2,
                );
                crate::leanh::lean_closure_set(v___x_3919_, 0, crate::leanh::lean_box(0));
                crate::leanh::lean_closure_set(v___x_3919_, 1, v_inst_3899_);
                v___x_3920_ =
                    l_Array_compareLex___redArg(v___x_3919_, v_title_3904_, v_title_3909_);
                crate::leanh::lean_dec_ref(v_title_3909_);
                crate::leanh::lean_dec_ref(v_title_3904_);
                if v___x_3920_ == 1 {
                    v___x_3921_ = lean_string_compare(v_titleString_3905_, v_titleString_3910_);
                    crate::leanh::lean_dec_ref(v_titleString_3910_);
                    crate::leanh::lean_dec_ref(v_titleString_3905_);
                    if v___x_3921_ == 1 {
                        if crate::leanh::lean_obj_tag(v_metadata_3906_) == 0 {
                            crate::leanh::lean_dec_ref(v_inst_3901_);
                            if crate::leanh::lean_obj_tag(v_metadata_3911_) == 0 {
                                state = 1;
                                continue;
                            } else {
                                crate::leanh::lean_dec_ref_known(v_metadata_3911_, 1);
                                crate::leanh::lean_dec_ref(v___x_3914_);
                                crate::leanh::lean_dec_ref(v_subParts_3913_);
                                crate::leanh::lean_dec_ref(v_content_3912_);
                                crate::leanh::lean_dec_ref(v_subParts_3908_);
                                crate::leanh::lean_dec_ref(v_content_3907_);
                                crate::leanh::lean_dec_ref(v_inst_3900_);
                                crate::leanh::lean_dec_ref(v_inst_3899_);
                                v___x_3922_ = 0;
                                return v___x_3922_;
                            }
                        } else {
                            if crate::leanh::lean_obj_tag(v_metadata_3911_) == 0 {
                                crate::leanh::lean_dec_ref_known(v_metadata_3906_, 1);
                                crate::leanh::lean_dec_ref(v___x_3914_);
                                crate::leanh::lean_dec_ref(v_subParts_3913_);
                                crate::leanh::lean_dec_ref(v_content_3912_);
                                crate::leanh::lean_dec_ref(v_subParts_3908_);
                                crate::leanh::lean_dec_ref(v_content_3907_);
                                crate::leanh::lean_dec_ref(v_inst_3901_);
                                crate::leanh::lean_dec_ref(v_inst_3900_);
                                crate::leanh::lean_dec_ref(v_inst_3899_);
                                v___x_3923_ = 2;
                                return v___x_3923_;
                            } else {
                                v_val_3924_ = crate::leanh::lean_ctor_get(v_metadata_3906_, 0);
                                crate::leanh::lean_inc(v_val_3924_);
                                crate::leanh::lean_dec_ref_known(v_metadata_3906_, 1);
                                v_val_3925_ = crate::leanh::lean_ctor_get(v_metadata_3911_, 0);
                                crate::leanh::lean_inc(v_val_3925_);
                                crate::leanh::lean_dec_ref_known(v_metadata_3911_, 1);
                                v___x_3926_ = crate::leanh::lean_apply_2(
                                    v_inst_3901_,
                                    v_val_3924_,
                                    v_val_3925_,
                                );
                                v___x_3927_ = (crate::leanh::lean_unbox(v___x_3926_) as u8);
                                if v___x_3927_ == 1 {
                                    state = 1;
                                    continue;
                                } else {
                                    crate::leanh::lean_dec_ref(v___x_3914_);
                                    crate::leanh::lean_dec_ref(v_subParts_3913_);
                                    crate::leanh::lean_dec_ref(v_content_3912_);
                                    crate::leanh::lean_dec_ref(v_subParts_3908_);
                                    crate::leanh::lean_dec_ref(v_content_3907_);
                                    crate::leanh::lean_dec_ref(v_inst_3900_);
                                    crate::leanh::lean_dec_ref(v_inst_3899_);
                                    v___x_3928_ = (crate::leanh::lean_unbox(v___x_3926_) as u8);
                                    return v___x_3928_;
                                }
                            }
                        }
                    } else {
                        crate::leanh::lean_dec_ref(v___x_3914_);
                        crate::leanh::lean_dec_ref(v_subParts_3913_);
                        crate::leanh::lean_dec_ref(v_content_3912_);
                        crate::leanh::lean_dec(v_metadata_3911_);
                        crate::leanh::lean_dec_ref(v_subParts_3908_);
                        crate::leanh::lean_dec_ref(v_content_3907_);
                        crate::leanh::lean_dec(v_metadata_3906_);
                        crate::leanh::lean_dec_ref(v_inst_3901_);
                        crate::leanh::lean_dec_ref(v_inst_3900_);
                        crate::leanh::lean_dec_ref(v_inst_3899_);
                        return v___x_3921_;
                    }
                } else {
                    crate::leanh::lean_dec_ref(v___x_3914_);
                    crate::leanh::lean_dec_ref(v_subParts_3913_);
                    crate::leanh::lean_dec_ref(v_content_3912_);
                    crate::leanh::lean_dec(v_metadata_3911_);
                    crate::leanh::lean_dec_ref(v_titleString_3910_);
                    crate::leanh::lean_dec_ref(v_subParts_3908_);
                    crate::leanh::lean_dec_ref(v_content_3907_);
                    crate::leanh::lean_dec(v_metadata_3906_);
                    crate::leanh::lean_dec_ref(v_titleString_3905_);
                    crate::leanh::lean_dec_ref(v_inst_3901_);
                    crate::leanh::lean_dec_ref(v_inst_3900_);
                    crate::leanh::lean_dec_ref(v_inst_3899_);
                    return v___x_3920_;
                }
            }
            1 => {
                v___x_3916_ = crate::leanh::lean_alloc_closure(
                    l_Lean_Doc_instOrdBlock_ord___boxed as *mut core::ffi::c_void,
                    6,
                    4,
                );
                crate::leanh::lean_closure_set(v___x_3916_, 0, crate::leanh::lean_box(0));
                crate::leanh::lean_closure_set(v___x_3916_, 1, crate::leanh::lean_box(0));
                crate::leanh::lean_closure_set(v___x_3916_, 2, v_inst_3899_);
                crate::leanh::lean_closure_set(v___x_3916_, 3, v_inst_3900_);
                v___x_3917_ =
                    l_Array_compareLex___redArg(v___x_3916_, v_content_3907_, v_content_3912_);
                crate::leanh::lean_dec_ref(v_content_3912_);
                crate::leanh::lean_dec_ref(v_content_3907_);
                if v___x_3917_ == 1 {
                    v___x_3918_ = l_Array_compareLex___redArg(
                        v___x_3914_,
                        v_subParts_3908_,
                        v_subParts_3913_,
                    );
                    crate::leanh::lean_dec_ref(v_subParts_3913_);
                    crate::leanh::lean_dec_ref(v_subParts_3908_);
                    if v___x_3918_ == 1 {
                        return v___x_3918_;
                    } else {
                        return v___x_3918_;
                    }
                } else {
                    crate::leanh::lean_dec_ref(v___x_3914_);
                    crate::leanh::lean_dec_ref(v_subParts_3913_);
                    crate::leanh::lean_dec_ref(v_subParts_3908_);
                    return v___x_3917_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Doc_instOrdPart_ord(
    mut v_i_3929_: *mut crate::leanh::LeanObject,
    mut v_b_3930_: *mut crate::leanh::LeanObject,
    mut v_p_3931_: *mut crate::leanh::LeanObject,
    mut v_inst_3932_: *mut crate::leanh::LeanObject,
    mut v_inst_3933_: *mut crate::leanh::LeanObject,
    mut v_inst_3934_: *mut crate::leanh::LeanObject,
    mut v_x_3935_: *mut crate::leanh::LeanObject,
    mut v_x_3936_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_3937_: u8 = 0;
    v___x_3937_ = l_Lean_Doc_instOrdPart_ord___redArg(
        v_inst_3932_,
        v_inst_3933_,
        v_inst_3934_,
        v_x_3935_,
        v_x_3936_,
    );
    return v___x_3937_;
}
pub unsafe fn l_Lean_Doc_instOrdPart_ord___boxed(
    mut v_i_3938_: *mut crate::leanh::LeanObject,
    mut v_b_3939_: *mut crate::leanh::LeanObject,
    mut v_p_3940_: *mut crate::leanh::LeanObject,
    mut v_inst_3941_: *mut crate::leanh::LeanObject,
    mut v_inst_3942_: *mut crate::leanh::LeanObject,
    mut v_inst_3943_: *mut crate::leanh::LeanObject,
    mut v_x_3944_: *mut crate::leanh::LeanObject,
    mut v_x_3945_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3946_: u8 = 0;
    let mut v_r_3947_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3946_ = l_Lean_Doc_instOrdPart_ord(
        v_i_3938_,
        v_b_3939_,
        v_p_3940_,
        v_inst_3941_,
        v_inst_3942_,
        v_inst_3943_,
        v_x_3944_,
        v_x_3945_,
    );
    v_r_3947_ = crate::leanh::lean_box((v_res_3946_) as usize);
    return v_r_3947_;
}
pub unsafe fn l_Lean_Doc_instOrdPart___redArg(
    mut v_inst_3948_: *mut crate::leanh::LeanObject,
    mut v_inst_3949_: *mut crate::leanh::LeanObject,
    mut v_inst_3950_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3951_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3951_ = crate::leanh::lean_alloc_closure(
        l_Lean_Doc_instOrdPart_ord___boxed as *mut core::ffi::c_void,
        8,
        6,
    );
    crate::leanh::lean_closure_set(v___x_3951_, 0, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_3951_, 1, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_3951_, 2, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_3951_, 3, v_inst_3948_);
    crate::leanh::lean_closure_set(v___x_3951_, 4, v_inst_3949_);
    crate::leanh::lean_closure_set(v___x_3951_, 5, v_inst_3950_);
    return v___x_3951_;
}
pub unsafe fn l_Lean_Doc_instOrdPart(
    mut v_i_3952_: *mut crate::leanh::LeanObject,
    mut v_b_3953_: *mut crate::leanh::LeanObject,
    mut v_p_3954_: *mut crate::leanh::LeanObject,
    mut v_inst_3955_: *mut crate::leanh::LeanObject,
    mut v_inst_3956_: *mut crate::leanh::LeanObject,
    mut v_inst_3957_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3958_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3958_ = crate::leanh::lean_alloc_closure(
        l_Lean_Doc_instOrdPart_ord___boxed as *mut core::ffi::c_void,
        8,
        6,
    );
    crate::leanh::lean_closure_set(v___x_3958_, 0, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_3958_, 1, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_3958_, 2, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_3958_, 3, v_inst_3955_);
    crate::leanh::lean_closure_set(v___x_3958_, 4, v_inst_3956_);
    crate::leanh::lean_closure_set(v___x_3958_, 5, v_inst_3957_);
    return v___x_3958_;
}
pub unsafe fn _init_l_Lean_Doc_instReprPart_repr___redArg___closed__4()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3968_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3969_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3968_ = crate::leanh::lean_unsigned_to_nat(9);
    v___x_3969_ = lean_nat_to_int(v___x_3968_);
    return v___x_3969_;
}
pub unsafe fn _init_l_Lean_Doc_instReprPart_repr___redArg___closed__7()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3973_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3974_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3973_ = crate::leanh::lean_unsigned_to_nat(15);
    v___x_3974_ = lean_nat_to_int(v___x_3973_);
    return v___x_3974_;
}
pub unsafe fn _init_l_Lean_Doc_instReprPart_repr___redArg___closed__12()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3981_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3982_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3981_ = crate::leanh::lean_unsigned_to_nat(11);
    v___x_3982_ = lean_nat_to_int(v___x_3981_);
    return v___x_3982_;
}
pub unsafe fn l_Lean_Doc_instReprPart_repr___redArg___boxed(
    mut v_inst_3986_: *mut crate::leanh::LeanObject,
    mut v_inst_3987_: *mut crate::leanh::LeanObject,
    mut v_inst_3988_: *mut crate::leanh::LeanObject,
    mut v_x_3989_: *mut crate::leanh::LeanObject,
    mut v_prec_3990_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3991_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3991_ = l_Lean_Doc_instReprPart_repr___redArg(
        v_inst_3986_,
        v_inst_3987_,
        v_inst_3988_,
        v_x_3989_,
        v_prec_3990_,
    );
    crate::leanh::lean_dec(v_prec_3990_);
    return v_res_3991_;
}
pub unsafe fn l_Lean_Doc_instReprPart_repr___redArg(
    mut v_inst_3992_: *mut crate::leanh::LeanObject,
    mut v_inst_3993_: *mut crate::leanh::LeanObject,
    mut v_inst_3994_: *mut crate::leanh::LeanObject,
    mut v_x_3995_: *mut crate::leanh::LeanObject,
    mut v_prec_3996_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_title_3997_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_titleString_3998_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_metadata_3999_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_content_4000_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_subParts_4001_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_localinst_4002_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4003_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4004_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4005_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4006_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4007_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4008_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4009_: u8 = 0;
    let mut v___x_4010_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4011_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4012_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4013_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4014_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4015_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4016_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4017_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4018_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4019_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4020_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4021_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4022_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4023_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4024_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4025_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4026_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4027_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4028_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4029_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4030_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4031_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4032_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4033_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4034_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4035_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4036_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4037_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4038_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4039_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4040_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4041_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4042_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4043_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4044_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4045_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4046_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4047_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4048_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4049_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4050_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4051_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4052_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4053_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4054_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4055_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4056_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4057_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4058_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4059_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4060_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4061_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4062_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_title_3997_ = crate::leanh::lean_ctor_get(v_x_3995_, 0);
    crate::leanh::lean_inc_ref(v_title_3997_);
    v_titleString_3998_ = crate::leanh::lean_ctor_get(v_x_3995_, 1);
    crate::leanh::lean_inc_ref(v_titleString_3998_);
    v_metadata_3999_ = crate::leanh::lean_ctor_get(v_x_3995_, 2);
    crate::leanh::lean_inc(v_metadata_3999_);
    v_content_4000_ = crate::leanh::lean_ctor_get(v_x_3995_, 3);
    crate::leanh::lean_inc_ref(v_content_4000_);
    v_subParts_4001_ = crate::leanh::lean_ctor_get(v_x_3995_, 4);
    crate::leanh::lean_inc_ref(v_subParts_4001_);
    crate::leanh::lean_dec_ref(v_x_3995_);
    crate::leanh::lean_inc_ref(v_inst_3994_);
    crate::leanh::lean_inc_ref(v_inst_3993_);
    crate::leanh::lean_inc_ref_n(v_inst_3992_, 2);
    v_localinst_4002_ = crate::leanh::lean_alloc_closure(
        l_Lean_Doc_instReprPart_repr___redArg___boxed as *mut core::ffi::c_void,
        5,
        3,
    );
    crate::leanh::lean_closure_set(v_localinst_4002_, 0, v_inst_3992_);
    crate::leanh::lean_closure_set(v_localinst_4002_, 1, v_inst_3993_);
    crate::leanh::lean_closure_set(v_localinst_4002_, 2, v_inst_3994_);
    v___x_4003_ = l_Lean_Doc_instReprListItem_repr___redArg___closed__5;
    v___x_4004_ = l_Lean_Doc_instReprPart_repr___redArg___closed__3;
    v___x_4005_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Doc_instReprPart_repr___redArg___closed__4),
        core::ptr::addr_of_mut!(l_Lean_Doc_instReprPart_repr___redArg___closed__4_once),
        _init_l_Lean_Doc_instReprPart_repr___redArg___closed__4,
    );
    v___x_4006_ = crate::leanh::lean_alloc_closure(
        l_Lean_Doc_instReprInline_repr___boxed as *mut core::ffi::c_void,
        4,
        2,
    );
    crate::leanh::lean_closure_set(v___x_4006_, 0, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_4006_, 1, v_inst_3992_);
    v___x_4007_ = l_Array_repr___redArg(v___x_4006_, v_title_3997_);
    v___x_4008_ = crate::leanh::lean_alloc_ctor(4, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_4008_, 0, v___x_4005_);
    crate::leanh::lean_ctor_set(v___x_4008_, 1, v___x_4007_);
    v___x_4009_ = 0;
    v___x_4010_ = crate::leanh::lean_alloc_ctor(6, 1, (1) as u32);
    crate::leanh::lean_ctor_set(v___x_4010_, 0, v___x_4008_);
    crate::leanh::lean_ctor_set_uint8(
        v___x_4010_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
        v___x_4009_,
    );
    v___x_4011_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_4011_, 0, v___x_4004_);
    crate::leanh::lean_ctor_set(v___x_4011_, 1, v___x_4010_);
    v___x_4012_ = l_Lean_Doc_instReprDescItem_repr___redArg___closed__6;
    v___x_4013_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_4013_, 0, v___x_4011_);
    crate::leanh::lean_ctor_set(v___x_4013_, 1, v___x_4012_);
    v___x_4014_ = crate::leanh::lean_box(1);
    v___x_4015_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_4015_, 0, v___x_4013_);
    crate::leanh::lean_ctor_set(v___x_4015_, 1, v___x_4014_);
    v___x_4016_ = l_Lean_Doc_instReprPart_repr___redArg___closed__6;
    v___x_4017_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_4017_, 0, v___x_4015_);
    crate::leanh::lean_ctor_set(v___x_4017_, 1, v___x_4016_);
    v___x_4018_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_4018_, 0, v___x_4017_);
    crate::leanh::lean_ctor_set(v___x_4018_, 1, v___x_4003_);
    v___x_4019_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Doc_instReprPart_repr___redArg___closed__7),
        core::ptr::addr_of_mut!(l_Lean_Doc_instReprPart_repr___redArg___closed__7_once),
        _init_l_Lean_Doc_instReprPart_repr___redArg___closed__7,
    );
    v___x_4020_ = l_String_quote(v_titleString_3998_);
    v___x_4021_ = crate::leanh::lean_alloc_ctor(3, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_4021_, 0, v___x_4020_);
    v___x_4022_ = crate::leanh::lean_alloc_ctor(4, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_4022_, 0, v___x_4019_);
    crate::leanh::lean_ctor_set(v___x_4022_, 1, v___x_4021_);
    v___x_4023_ = crate::leanh::lean_alloc_ctor(6, 1, (1) as u32);
    crate::leanh::lean_ctor_set(v___x_4023_, 0, v___x_4022_);
    crate::leanh::lean_ctor_set_uint8(
        v___x_4023_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
        v___x_4009_,
    );
    v___x_4024_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_4024_, 0, v___x_4018_);
    crate::leanh::lean_ctor_set(v___x_4024_, 1, v___x_4023_);
    v___x_4025_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_4025_, 0, v___x_4024_);
    crate::leanh::lean_ctor_set(v___x_4025_, 1, v___x_4012_);
    v___x_4026_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_4026_, 0, v___x_4025_);
    crate::leanh::lean_ctor_set(v___x_4026_, 1, v___x_4014_);
    v___x_4027_ = l_Lean_Doc_instReprPart_repr___redArg___closed__9;
    v___x_4028_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_4028_, 0, v___x_4026_);
    crate::leanh::lean_ctor_set(v___x_4028_, 1, v___x_4027_);
    v___x_4029_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_4029_, 0, v___x_4028_);
    crate::leanh::lean_ctor_set(v___x_4029_, 1, v___x_4003_);
    v___x_4030_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Doc_instReprListItem_repr___redArg___closed__7),
        core::ptr::addr_of_mut!(l_Lean_Doc_instReprListItem_repr___redArg___closed__7_once),
        _init_l_Lean_Doc_instReprListItem_repr___redArg___closed__7,
    );
    v___x_4031_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_4032_ = l_Option_repr___redArg(v_inst_3994_, v_metadata_3999_, v___x_4031_);
    v___x_4033_ = crate::leanh::lean_alloc_ctor(4, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_4033_, 0, v___x_4030_);
    crate::leanh::lean_ctor_set(v___x_4033_, 1, v___x_4032_);
    v___x_4034_ = crate::leanh::lean_alloc_ctor(6, 1, (1) as u32);
    crate::leanh::lean_ctor_set(v___x_4034_, 0, v___x_4033_);
    crate::leanh::lean_ctor_set_uint8(
        v___x_4034_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
        v___x_4009_,
    );
    v___x_4035_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_4035_, 0, v___x_4029_);
    crate::leanh::lean_ctor_set(v___x_4035_, 1, v___x_4034_);
    v___x_4036_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_4036_, 0, v___x_4035_);
    crate::leanh::lean_ctor_set(v___x_4036_, 1, v___x_4012_);
    v___x_4037_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_4037_, 0, v___x_4036_);
    crate::leanh::lean_ctor_set(v___x_4037_, 1, v___x_4014_);
    v___x_4038_ = l_Lean_Doc_instReprPart_repr___redArg___closed__11;
    v___x_4039_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_4039_, 0, v___x_4037_);
    crate::leanh::lean_ctor_set(v___x_4039_, 1, v___x_4038_);
    v___x_4040_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_4040_, 0, v___x_4039_);
    crate::leanh::lean_ctor_set(v___x_4040_, 1, v___x_4003_);
    v___x_4041_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Doc_instReprPart_repr___redArg___closed__12),
        core::ptr::addr_of_mut!(l_Lean_Doc_instReprPart_repr___redArg___closed__12_once),
        _init_l_Lean_Doc_instReprPart_repr___redArg___closed__12,
    );
    v___x_4042_ = crate::leanh::lean_alloc_closure(
        l_Lean_Doc_instReprBlock_repr___boxed as *mut core::ffi::c_void,
        6,
        4,
    );
    crate::leanh::lean_closure_set(v___x_4042_, 0, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_4042_, 1, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_4042_, 2, v_inst_3992_);
    crate::leanh::lean_closure_set(v___x_4042_, 3, v_inst_3993_);
    v___x_4043_ = l_Array_repr___redArg(v___x_4042_, v_content_4000_);
    v___x_4044_ = crate::leanh::lean_alloc_ctor(4, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_4044_, 0, v___x_4041_);
    crate::leanh::lean_ctor_set(v___x_4044_, 1, v___x_4043_);
    v___x_4045_ = crate::leanh::lean_alloc_ctor(6, 1, (1) as u32);
    crate::leanh::lean_ctor_set(v___x_4045_, 0, v___x_4044_);
    crate::leanh::lean_ctor_set_uint8(
        v___x_4045_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
        v___x_4009_,
    );
    v___x_4046_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_4046_, 0, v___x_4040_);
    crate::leanh::lean_ctor_set(v___x_4046_, 1, v___x_4045_);
    v___x_4047_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_4047_, 0, v___x_4046_);
    crate::leanh::lean_ctor_set(v___x_4047_, 1, v___x_4012_);
    v___x_4048_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_4048_, 0, v___x_4047_);
    crate::leanh::lean_ctor_set(v___x_4048_, 1, v___x_4014_);
    v___x_4049_ = l_Lean_Doc_instReprPart_repr___redArg___closed__14;
    v___x_4050_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_4050_, 0, v___x_4048_);
    crate::leanh::lean_ctor_set(v___x_4050_, 1, v___x_4049_);
    v___x_4051_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_4051_, 0, v___x_4050_);
    crate::leanh::lean_ctor_set(v___x_4051_, 1, v___x_4003_);
    v___x_4052_ = l_Array_repr___redArg(v_localinst_4002_, v_subParts_4001_);
    v___x_4053_ = crate::leanh::lean_alloc_ctor(4, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_4053_, 0, v___x_4030_);
    crate::leanh::lean_ctor_set(v___x_4053_, 1, v___x_4052_);
    v___x_4054_ = crate::leanh::lean_alloc_ctor(6, 1, (1) as u32);
    crate::leanh::lean_ctor_set(v___x_4054_, 0, v___x_4053_);
    crate::leanh::lean_ctor_set_uint8(
        v___x_4054_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
        v___x_4009_,
    );
    v___x_4055_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_4055_, 0, v___x_4051_);
    crate::leanh::lean_ctor_set(v___x_4055_, 1, v___x_4054_);
    v___x_4056_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Doc_instReprListItem_repr___redArg___closed__10),
        core::ptr::addr_of_mut!(l_Lean_Doc_instReprListItem_repr___redArg___closed__10_once),
        _init_l_Lean_Doc_instReprListItem_repr___redArg___closed__10,
    );
    v___x_4057_ = l_Lean_Doc_instReprListItem_repr___redArg___closed__11;
    v___x_4058_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_4058_, 0, v___x_4057_);
    crate::leanh::lean_ctor_set(v___x_4058_, 1, v___x_4055_);
    v___x_4059_ = l_Lean_Doc_instReprListItem_repr___redArg___closed__12;
    v___x_4060_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_4060_, 0, v___x_4058_);
    crate::leanh::lean_ctor_set(v___x_4060_, 1, v___x_4059_);
    v___x_4061_ = crate::leanh::lean_alloc_ctor(4, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_4061_, 0, v___x_4056_);
    crate::leanh::lean_ctor_set(v___x_4061_, 1, v___x_4060_);
    v___x_4062_ = crate::leanh::lean_alloc_ctor(6, 1, (1) as u32);
    crate::leanh::lean_ctor_set(v___x_4062_, 0, v___x_4061_);
    crate::leanh::lean_ctor_set_uint8(
        v___x_4062_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
        v___x_4009_,
    );
    return v___x_4062_;
}
pub unsafe fn l_Lean_Doc_instReprPart_repr(
    mut v_i_4063_: *mut crate::leanh::LeanObject,
    mut v_b_4064_: *mut crate::leanh::LeanObject,
    mut v_p_4065_: *mut crate::leanh::LeanObject,
    mut v_inst_4066_: *mut crate::leanh::LeanObject,
    mut v_inst_4067_: *mut crate::leanh::LeanObject,
    mut v_inst_4068_: *mut crate::leanh::LeanObject,
    mut v_x_4069_: *mut crate::leanh::LeanObject,
    mut v_prec_4070_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4071_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4071_ = l_Lean_Doc_instReprPart_repr___redArg(
        v_inst_4066_,
        v_inst_4067_,
        v_inst_4068_,
        v_x_4069_,
        v_prec_4070_,
    );
    return v___x_4071_;
}
pub unsafe fn l_Lean_Doc_instReprPart_repr___boxed(
    mut v_i_4072_: *mut crate::leanh::LeanObject,
    mut v_b_4073_: *mut crate::leanh::LeanObject,
    mut v_p_4074_: *mut crate::leanh::LeanObject,
    mut v_inst_4075_: *mut crate::leanh::LeanObject,
    mut v_inst_4076_: *mut crate::leanh::LeanObject,
    mut v_inst_4077_: *mut crate::leanh::LeanObject,
    mut v_x_4078_: *mut crate::leanh::LeanObject,
    mut v_prec_4079_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4080_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4080_ = l_Lean_Doc_instReprPart_repr(
        v_i_4072_,
        v_b_4073_,
        v_p_4074_,
        v_inst_4075_,
        v_inst_4076_,
        v_inst_4077_,
        v_x_4078_,
        v_prec_4079_,
    );
    crate::leanh::lean_dec(v_prec_4079_);
    return v_res_4080_;
}
pub unsafe fn l_Lean_Doc_instReprPart___redArg(
    mut v_inst_4081_: *mut crate::leanh::LeanObject,
    mut v_inst_4082_: *mut crate::leanh::LeanObject,
    mut v_inst_4083_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4084_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4084_ = crate::leanh::lean_alloc_closure(
        l_Lean_Doc_instReprPart_repr___boxed as *mut core::ffi::c_void,
        8,
        6,
    );
    crate::leanh::lean_closure_set(v___x_4084_, 0, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_4084_, 1, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_4084_, 2, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_4084_, 3, v_inst_4081_);
    crate::leanh::lean_closure_set(v___x_4084_, 4, v_inst_4082_);
    crate::leanh::lean_closure_set(v___x_4084_, 5, v_inst_4083_);
    return v___x_4084_;
}
pub unsafe fn l_Lean_Doc_instReprPart(
    mut v_i_4085_: *mut crate::leanh::LeanObject,
    mut v_b_4086_: *mut crate::leanh::LeanObject,
    mut v_p_4087_: *mut crate::leanh::LeanObject,
    mut v_inst_4088_: *mut crate::leanh::LeanObject,
    mut v_inst_4089_: *mut crate::leanh::LeanObject,
    mut v_inst_4090_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4091_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4091_ = crate::leanh::lean_alloc_closure(
        l_Lean_Doc_instReprPart_repr___boxed as *mut core::ffi::c_void,
        8,
        6,
    );
    crate::leanh::lean_closure_set(v___x_4091_, 0, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_4091_, 1, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_4091_, 2, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_4091_, 3, v_inst_4088_);
    crate::leanh::lean_closure_set(v___x_4091_, 4, v_inst_4089_);
    crate::leanh::lean_closure_set(v___x_4091_, 5, v_inst_4090_);
    return v___x_4091_;
}
pub unsafe fn l_Lean_Doc_instInhabitedPart_default(
    mut v_i_4096_: *mut crate::leanh::LeanObject,
    mut v_b_4097_: *mut crate::leanh::LeanObject,
    mut v_p_4098_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4099_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4099_ = l_Lean_Doc_instInhabitedPart_default___closed__0;
    return v___x_4099_;
}
pub unsafe fn _init_l_Lean_Doc_instInhabitedPart___closed__0() -> *mut crate::leanh::LeanObject {
    let mut v___x_4100_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4100_ = l_Lean_Doc_instInhabitedPart_default(
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
    );
    return v___x_4100_;
}
pub unsafe fn l_Lean_Doc_instInhabitedPart(
    mut v_a_4101_: *mut crate::leanh::LeanObject,
    mut v_a_4102_: *mut crate::leanh::LeanObject,
    mut v_a_4103_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4104_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4104_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Doc_instInhabitedPart___closed__0),
        core::ptr::addr_of_mut!(l_Lean_Doc_instInhabitedPart___closed__0_once),
        _init_l_Lean_Doc_instInhabitedPart___closed__0,
    );
    return v___x_4104_;
}
pub unsafe fn l_Lean_Doc_Part_cast___redArg(
    mut v_x_4105_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc_ref(v_x_4105_);
    return v_x_4105_;
}
pub unsafe fn l_Lean_Doc_Part_cast___redArg___boxed(
    mut v_x_4106_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4107_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4107_ = l_Lean_Doc_Part_cast___redArg(v_x_4106_);
    crate::leanh::lean_dec_ref(v_x_4106_);
    return v_res_4107_;
}
pub unsafe fn l_Lean_Doc_Part_cast(
    mut v_i_4108_: *mut crate::leanh::LeanObject,
    mut v_i_x27_4109_: *mut crate::leanh::LeanObject,
    mut v_b_4110_: *mut crate::leanh::LeanObject,
    mut v_b_x27_4111_: *mut crate::leanh::LeanObject,
    mut v_p_4112_: *mut crate::leanh::LeanObject,
    mut v_p_x27_4113_: *mut crate::leanh::LeanObject,
    mut v_inlines__eq_4114_: *mut crate::leanh::LeanObject,
    mut v_blocks__eq_4115_: *mut crate::leanh::LeanObject,
    mut v_metadata__eq_4116_: *mut crate::leanh::LeanObject,
    mut v_x_4117_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc_ref(v_x_4117_);
    return v_x_4117_;
}
pub unsafe fn l_Lean_Doc_Part_cast___boxed(
    mut v_i_4118_: *mut crate::leanh::LeanObject,
    mut v_i_x27_4119_: *mut crate::leanh::LeanObject,
    mut v_b_4120_: *mut crate::leanh::LeanObject,
    mut v_b_x27_4121_: *mut crate::leanh::LeanObject,
    mut v_p_4122_: *mut crate::leanh::LeanObject,
    mut v_p_x27_4123_: *mut crate::leanh::LeanObject,
    mut v_inlines__eq_4124_: *mut crate::leanh::LeanObject,
    mut v_blocks__eq_4125_: *mut crate::leanh::LeanObject,
    mut v_metadata__eq_4126_: *mut crate::leanh::LeanObject,
    mut v_x_4127_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4128_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4128_ = l_Lean_Doc_Part_cast(
        v_i_4118_,
        v_i_x27_4119_,
        v_b_4120_,
        v_b_x27_4121_,
        v_p_4122_,
        v_p_x27_4123_,
        v_inlines__eq_4124_,
        v_blocks__eq_4125_,
        v_metadata__eq_4126_,
        v_x_4127_,
    );
    crate::leanh::lean_dec_ref(v_x_4127_);
    return v_res_4128_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_DocString_Types(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Init_Data_Ord(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Nat_Compare(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Array_GetLit(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_DocString_Types(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_meta_initialized = true;
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lean_DocString_Types(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Init_Data_Ord(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Data_Nat_Compare(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Data_Array_GetLit(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_DocString_Types(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Lean_DocString_Types(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Lean_DocString_Types(builtin);
}
