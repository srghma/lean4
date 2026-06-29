// Lean compiler output
// Module: Init.Data.Range.Polymorphic.UInt
// Imports: Init.Data.Range.Polymorphic.BitVec Init.Data.UInt Init.ByCases Init.Data.BitVec.Lemmas Init.Data.Option.Lemmas
use crate::r#gen::Init::ByCases::{initialize_Init_ByCases, runtime_initialize_Init_ByCases};
use crate::r#gen::Init::Data::BitVec::Lemmas::{
    initialize_Init_Data_BitVec_Lemmas, runtime_initialize_Init_Data_BitVec_Lemmas,
};
use crate::r#gen::Init::Data::Option::Lemmas::{
    initialize_Init_Data_Option_Lemmas, runtime_initialize_Init_Data_Option_Lemmas,
};
use crate::r#gen::Init::Data::Range::Polymorphic::BitVec::{
    initialize_Init_Data_Range_Polymorphic_BitVec,
    runtime_initialize_Init_Data_Range_Polymorphic_BitVec,
};
use crate::r#gen::Init::Data::UInt::{
    initialize_Init_Data_UInt, runtime_initialize_Init_Data_UInt,
};
use crate::r#gen::Init::Prelude::l_System_Platform_numBits;
use crate::ffi::{
    lean_uint8_add, lean_uint16_add, lean_uint64_add,
};
use crate::ffi::{
    lean_uint8_to_nat, lean_uint16_to_nat, lean_uint32_add, lean_uint64_to_nat, lean_usize_add,
    lean_usize_to_nat,
};
use crate::ffi::{
    lean_nat_add, lean_nat_dec_lt, lean_nat_pow, lean_nat_sub, lean_uint8_dec_eq,
    lean_uint8_of_nat, lean_uint16_dec_eq, lean_uint16_of_nat, lean_uint32_dec_eq,
    lean_uint32_of_nat, lean_uint32_to_nat, lean_uint64_dec_eq, lean_uint64_of_nat,
    lean_usize_dec_eq, lean_usize_of_nat,
};
pub static l_UInt8_instUpwardEnumerable___closed__0_value: crate::leanh::LeanClosureObject<0> =
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
        m_fun: l_UInt8_instUpwardEnumerable___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_UInt8_instUpwardEnumerable___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_UInt8_instUpwardEnumerable___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_UInt8_instUpwardEnumerable___closed__1_value: crate::leanh::LeanClosureObject<0> =
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
        m_fun: l_UInt8_instUpwardEnumerable___lam__1___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_UInt8_instUpwardEnumerable___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_UInt8_instUpwardEnumerable___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_UInt8_instUpwardEnumerable___closed__2_value: crate::leanh::LeanCtorObject<2> =
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
            core::ptr::addr_of!(l_UInt8_instUpwardEnumerable___closed__0_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_UInt8_instUpwardEnumerable___closed__1_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_UInt8_instUpwardEnumerable___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_UInt8_instUpwardEnumerable___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_UInt8_instUpwardEnumerable: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_UInt8_instUpwardEnumerable___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l_UInt8_instLeast_x3f___closed__0_value: crate::leanh::LeanCtorObject<1> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 1,
        },
        m_objs: [(((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject],
    };
static mut l_UInt8_instLeast_x3f___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_UInt8_instLeast_x3f___closed__0_value) as *mut crate::leanh::LeanObject;
pub static mut l_UInt8_instLeast_x3f: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_UInt8_instLeast_x3f___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_UInt8_instHasSize___closed__0_value: crate::leanh::LeanClosureObject<0> =
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
        m_fun: l_UInt8_instHasSize___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_UInt8_instHasSize___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_UInt8_instHasSize___closed__0_value) as *mut crate::leanh::LeanObject;
pub static mut l_UInt8_instHasSize: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_UInt8_instHasSize___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_UInt8_instHasSize__1___closed__0_value: crate::leanh::LeanClosureObject<0> =
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
        m_fun: l_UInt8_instHasSize__1___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_UInt8_instHasSize__1___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_UInt8_instHasSize__1___closed__0_value) as *mut crate::leanh::LeanObject;
pub static mut l_UInt8_instHasSize__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_UInt8_instHasSize__1___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_UInt8_instHasSize__2___closed__0_value: crate::leanh::LeanClosureObject<0> =
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
        m_fun: l_UInt8_instHasSize__2___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_UInt8_instHasSize__2___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_UInt8_instHasSize__2___closed__0_value) as *mut crate::leanh::LeanObject;
pub static mut l_UInt8_instHasSize__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_UInt8_instHasSize__2___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_UInt16_instUpwardEnumerable___closed__0_value: crate::leanh::LeanClosureObject<0> =
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
        m_fun: l_UInt16_instUpwardEnumerable___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_UInt16_instUpwardEnumerable___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_UInt16_instUpwardEnumerable___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_UInt16_instUpwardEnumerable___closed__1_value: crate::leanh::LeanClosureObject<0> =
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
        m_fun: l_UInt16_instUpwardEnumerable___lam__1___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_UInt16_instUpwardEnumerable___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_UInt16_instUpwardEnumerable___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_UInt16_instUpwardEnumerable___closed__2_value: crate::leanh::LeanCtorObject<2> =
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
            core::ptr::addr_of!(l_UInt16_instUpwardEnumerable___closed__0_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_UInt16_instUpwardEnumerable___closed__1_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_UInt16_instUpwardEnumerable___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_UInt16_instUpwardEnumerable___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_UInt16_instUpwardEnumerable: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_UInt16_instUpwardEnumerable___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l_UInt16_instLeast_x3f___closed__0_value: crate::leanh::LeanCtorObject<1> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 1,
        },
        m_objs: [(((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject],
    };
static mut l_UInt16_instLeast_x3f___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_UInt16_instLeast_x3f___closed__0_value) as *mut crate::leanh::LeanObject;
pub static mut l_UInt16_instLeast_x3f: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_UInt16_instLeast_x3f___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_UInt16_instHasSize___closed__0_value: crate::leanh::LeanClosureObject<0> =
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
        m_fun: l_UInt16_instHasSize___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_UInt16_instHasSize___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_UInt16_instHasSize___closed__0_value) as *mut crate::leanh::LeanObject;
pub static mut l_UInt16_instHasSize: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_UInt16_instHasSize___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_UInt16_instHasSize__1___closed__0_value: crate::leanh::LeanClosureObject<0> =
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
        m_fun: l_UInt16_instHasSize__1___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_UInt16_instHasSize__1___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_UInt16_instHasSize__1___closed__0_value) as *mut crate::leanh::LeanObject;
pub static mut l_UInt16_instHasSize__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_UInt16_instHasSize__1___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_UInt16_instHasSize__2___closed__0_value: crate::leanh::LeanClosureObject<0> =
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
        m_fun: l_UInt16_instHasSize__2___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_UInt16_instHasSize__2___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_UInt16_instHasSize__2___closed__0_value) as *mut crate::leanh::LeanObject;
pub static mut l_UInt16_instHasSize__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_UInt16_instHasSize__2___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_UInt32_instUpwardEnumerable___closed__0_value: crate::leanh::LeanClosureObject<0> =
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
        m_fun: l_UInt32_instUpwardEnumerable___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_UInt32_instUpwardEnumerable___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_UInt32_instUpwardEnumerable___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_UInt32_instUpwardEnumerable___closed__1_value: crate::leanh::LeanClosureObject<0> =
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
        m_fun: l_UInt32_instUpwardEnumerable___lam__1___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_UInt32_instUpwardEnumerable___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_UInt32_instUpwardEnumerable___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_UInt32_instUpwardEnumerable___closed__2_value: crate::leanh::LeanCtorObject<2> =
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
            core::ptr::addr_of!(l_UInt32_instUpwardEnumerable___closed__0_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_UInt32_instUpwardEnumerable___closed__1_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_UInt32_instUpwardEnumerable___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_UInt32_instUpwardEnumerable___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_UInt32_instUpwardEnumerable: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_UInt32_instUpwardEnumerable___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_UInt32_instLeast_x3f___closed__0___boxed__const__1: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_UInt32_instLeast_x3f___closed__0_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_UInt32_instLeast_x3f___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static mut l_UInt32_instLeast_x3f: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_UInt32_instHasSize___closed__0_value: crate::leanh::LeanClosureObject<0> =
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
        m_fun: l_UInt32_instHasSize___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_UInt32_instHasSize___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_UInt32_instHasSize___closed__0_value) as *mut crate::leanh::LeanObject;
pub static mut l_UInt32_instHasSize: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_UInt32_instHasSize___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_UInt32_instHasSize__1___closed__0_value: crate::leanh::LeanClosureObject<0> =
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
        m_fun: l_UInt32_instHasSize__1___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_UInt32_instHasSize__1___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_UInt32_instHasSize__1___closed__0_value) as *mut crate::leanh::LeanObject;
pub static mut l_UInt32_instHasSize__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_UInt32_instHasSize__1___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_UInt32_instHasSize__2___closed__0_value: crate::leanh::LeanClosureObject<0> =
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
        m_fun: l_UInt32_instHasSize__2___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_UInt32_instHasSize__2___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_UInt32_instHasSize__2___closed__0_value) as *mut crate::leanh::LeanObject;
pub static mut l_UInt32_instHasSize__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_UInt32_instHasSize__2___closed__0_value) as *mut crate::leanh::LeanObject;
static mut l_UInt64_instUpwardEnumerable___lam__1___closed__0_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_UInt64_instUpwardEnumerable___lam__1___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_UInt64_instUpwardEnumerable___closed__0_value: crate::leanh::LeanClosureObject<0> =
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
        m_fun: l_UInt64_instUpwardEnumerable___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_UInt64_instUpwardEnumerable___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_UInt64_instUpwardEnumerable___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_UInt64_instUpwardEnumerable___closed__1_value: crate::leanh::LeanClosureObject<0> =
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
        m_fun: l_UInt64_instUpwardEnumerable___lam__1___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_UInt64_instUpwardEnumerable___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_UInt64_instUpwardEnumerable___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_UInt64_instUpwardEnumerable___closed__2_value: crate::leanh::LeanCtorObject<2> =
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
            core::ptr::addr_of!(l_UInt64_instUpwardEnumerable___closed__0_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_UInt64_instUpwardEnumerable___closed__1_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_UInt64_instUpwardEnumerable___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_UInt64_instUpwardEnumerable___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_UInt64_instUpwardEnumerable: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_UInt64_instUpwardEnumerable___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l_UInt64_instLeast_x3f___closed__0___boxed__const__1_value:
    crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 0
            + 8) as u16,
        other: 0,
        tag: 0,
    },
    m_objs: [0 as *mut crate::leanh::LeanObject],
};
pub static mut l_UInt64_instLeast_x3f___closed__0___boxed__const__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_UInt64_instLeast_x3f___closed__0___boxed__const__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_UInt64_instLeast_x3f___closed__0_value: crate::leanh::LeanCtorObject<1> =
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
            core::ptr::addr_of!(l_UInt64_instLeast_x3f___closed__0___boxed__const__1_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_UInt64_instLeast_x3f___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_UInt64_instLeast_x3f___closed__0_value) as *mut crate::leanh::LeanObject;
pub static mut l_UInt64_instLeast_x3f: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_UInt64_instLeast_x3f___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_UInt64_instHasSize___closed__0_value: crate::leanh::LeanClosureObject<0> =
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
        m_fun: l_UInt64_instHasSize___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_UInt64_instHasSize___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_UInt64_instHasSize___closed__0_value) as *mut crate::leanh::LeanObject;
pub static mut l_UInt64_instHasSize: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_UInt64_instHasSize___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_UInt64_instHasSize__1___closed__0_value: crate::leanh::LeanClosureObject<0> =
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
        m_fun: l_UInt64_instHasSize__1___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_UInt64_instHasSize__1___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_UInt64_instHasSize__1___closed__0_value) as *mut crate::leanh::LeanObject;
pub static mut l_UInt64_instHasSize__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_UInt64_instHasSize__1___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_UInt64_instHasSize__2___closed__0_value: crate::leanh::LeanClosureObject<0> =
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
        m_fun: l_UInt64_instHasSize__2___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_UInt64_instHasSize__2___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_UInt64_instHasSize__2___closed__0_value) as *mut crate::leanh::LeanObject;
pub static mut l_UInt64_instHasSize__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_UInt64_instHasSize__2___closed__0_value) as *mut crate::leanh::LeanObject;
static mut l_USize_instUpwardEnumerable___lam__1___closed__0_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_USize_instUpwardEnumerable___lam__1___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_USize_instUpwardEnumerable___closed__0_value: crate::leanh::LeanClosureObject<0> =
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
        m_fun: l_USize_instUpwardEnumerable___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_USize_instUpwardEnumerable___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_USize_instUpwardEnumerable___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_USize_instUpwardEnumerable___closed__1_value: crate::leanh::LeanClosureObject<0> =
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
        m_fun: l_USize_instUpwardEnumerable___lam__1___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_USize_instUpwardEnumerable___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_USize_instUpwardEnumerable___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_USize_instUpwardEnumerable___closed__2_value: crate::leanh::LeanCtorObject<2> =
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
            core::ptr::addr_of!(l_USize_instUpwardEnumerable___closed__0_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_USize_instUpwardEnumerable___closed__1_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_USize_instUpwardEnumerable___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_USize_instUpwardEnumerable___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_USize_instUpwardEnumerable: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_USize_instUpwardEnumerable___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l_USize_instLeast_x3f___closed__0___boxed__const__1_value: crate::leanh::LeanCtorObject<
    1,
> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
            + core::mem::size_of::<usize>() * 1) as u16,
        other: 1,
        tag: 0,
    },
    m_objs: [(0 as *mut crate::leanh::LeanObject)],
};
pub static mut l_USize_instLeast_x3f___closed__0___boxed__const__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_USize_instLeast_x3f___closed__0___boxed__const__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_USize_instLeast_x3f___closed__0_value: crate::leanh::LeanCtorObject<1> =
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
            core::ptr::addr_of!(l_USize_instLeast_x3f___closed__0___boxed__const__1_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_USize_instLeast_x3f___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_USize_instLeast_x3f___closed__0_value) as *mut crate::leanh::LeanObject;
pub static mut l_USize_instLeast_x3f: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_USize_instLeast_x3f___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_USize_instHasSize___closed__0_value: crate::leanh::LeanClosureObject<0> =
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
        m_fun: l_USize_instHasSize___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_USize_instHasSize___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_USize_instHasSize___closed__0_value) as *mut crate::leanh::LeanObject;
pub static mut l_USize_instHasSize: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_USize_instHasSize___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_USize_instHasSize__1___closed__0_value: crate::leanh::LeanClosureObject<0> =
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
        m_fun: l_USize_instHasSize__1___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_USize_instHasSize__1___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_USize_instHasSize__1___closed__0_value) as *mut crate::leanh::LeanObject;
pub static mut l_USize_instHasSize__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_USize_instHasSize__1___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_USize_instHasSize__2___closed__0_value: crate::leanh::LeanClosureObject<0> =
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
        m_fun: l_USize_instHasSize__2___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_USize_instHasSize__2___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_USize_instHasSize__2___closed__0_value) as *mut crate::leanh::LeanObject;
pub static mut l_USize_instHasSize__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_USize_instHasSize__2___closed__0_value) as *mut crate::leanh::LeanObject;
pub unsafe fn l_UInt8_instUpwardEnumerable___lam__0(
    mut v_i_373_: u8,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_374_: u8 = 0;
    let mut v___x_375_: u8 = 0;
    let mut v___x_376_: u8 = 0;
    let mut v___x_377_: u8 = 0;
    v___x_374_ = 1;
    v___x_375_ = lean_uint8_add(v_i_373_, v___x_374_);
    v___x_376_ = 0;
    v___x_377_ = lean_uint8_dec_eq(v___x_375_, v___x_376_);
    if v___x_377_ == 0 {
        let mut v___x_378_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_379_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_378_ = crate::leanh::lean_box((v___x_375_) as usize);
        v___x_379_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_379_, 0, v___x_378_);
        return v___x_379_;
    } else {
        let mut v___x_380_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_380_ = crate::leanh::lean_box(0);
        return v___x_380_;
    }
}
pub unsafe fn l_UInt8_instUpwardEnumerable___lam__0___boxed(
    mut v_i_381_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_i_boxed_382_: u8 = 0;
    let mut v_res_383_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_i_boxed_382_ = (crate::leanh::lean_unbox(v_i_381_) as u8);
    v_res_383_ = l_UInt8_instUpwardEnumerable___lam__0(v_i_boxed_382_);
    return v_res_383_;
}
pub unsafe fn l_UInt8_instUpwardEnumerable___lam__1(
    mut v_n_384_: *mut crate::leanh::LeanObject,
    mut v_i_385_: u8,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_386_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_387_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_388_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_389_: u8 = 0;
    v___x_386_ = lean_uint8_to_nat(v_i_385_);
    v___x_387_ = lean_nat_add(v___x_386_, v_n_384_);
    v___x_388_ = crate::leanh::lean_unsigned_to_nat(256);
    v___x_389_ = lean_nat_dec_lt(v___x_387_, v___x_388_);
    if v___x_389_ == 0 {
        let mut v___x_390_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v___x_387_);
        v___x_390_ = crate::leanh::lean_box(0);
        return v___x_390_;
    } else {
        let mut v___x_391_: u8 = 0;
        let mut v___x_392_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_393_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_391_ = lean_uint8_of_nat(v___x_387_);
        crate::leanh::lean_dec(v___x_387_);
        v___x_392_ = crate::leanh::lean_box((v___x_391_) as usize);
        v___x_393_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_393_, 0, v___x_392_);
        return v___x_393_;
    }
}
pub unsafe fn l_UInt8_instUpwardEnumerable___lam__1___boxed(
    mut v_n_394_: *mut crate::leanh::LeanObject,
    mut v_i_395_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_i_boxed_396_: u8 = 0;
    let mut v_res_397_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_i_boxed_396_ = (crate::leanh::lean_unbox(v_i_395_) as u8);
    v_res_397_ = l_UInt8_instUpwardEnumerable___lam__1(v_n_394_, v_i_boxed_396_);
    crate::leanh::lean_dec(v_n_394_);
    return v_res_397_;
}
pub unsafe fn l_UInt8_instHasSize___lam__0(
    mut v_lo_408_: u8,
    mut v_hi_409_: u8,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_410_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_411_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_412_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_413_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_414_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_410_ = lean_uint8_to_nat(v_hi_409_);
    v___x_411_ = crate::leanh::lean_unsigned_to_nat(1);
    v___x_412_ = lean_nat_add(v___x_410_, v___x_411_);
    v___x_413_ = lean_uint8_to_nat(v_lo_408_);
    v___x_414_ = lean_nat_sub(v___x_412_, v___x_413_);
    crate::leanh::lean_dec(v___x_412_);
    return v___x_414_;
}
pub unsafe fn l_UInt8_instHasSize___lam__0___boxed(
    mut v_lo_415_: *mut crate::leanh::LeanObject,
    mut v_hi_416_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_lo_boxed_417_: u8 = 0;
    let mut v_hi_boxed_418_: u8 = 0;
    let mut v_res_419_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_lo_boxed_417_ = (crate::leanh::lean_unbox(v_lo_415_) as u8);
    v_hi_boxed_418_ = (crate::leanh::lean_unbox(v_hi_416_) as u8);
    v_res_419_ = l_UInt8_instHasSize___lam__0(v_lo_boxed_417_, v_hi_boxed_418_);
    return v_res_419_;
}
pub unsafe fn l_UInt8_instHasSize__1___lam__0(
    mut v_lo_422_: u8,
    mut v_hi_423_: u8,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_424_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_425_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_426_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_427_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_428_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_429_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_424_ = lean_uint8_to_nat(v_hi_423_);
    v___x_425_ = crate::leanh::lean_unsigned_to_nat(1);
    v___x_426_ = lean_nat_add(v___x_424_, v___x_425_);
    v___x_427_ = lean_uint8_to_nat(v_lo_422_);
    v___x_428_ = lean_nat_sub(v___x_426_, v___x_427_);
    crate::leanh::lean_dec(v___x_426_);
    v___x_429_ = lean_nat_sub(v___x_428_, v___x_425_);
    crate::leanh::lean_dec(v___x_428_);
    return v___x_429_;
}
pub unsafe fn l_UInt8_instHasSize__1___lam__0___boxed(
    mut v_lo_430_: *mut crate::leanh::LeanObject,
    mut v_hi_431_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_lo_boxed_432_: u8 = 0;
    let mut v_hi_boxed_433_: u8 = 0;
    let mut v_res_434_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_lo_boxed_432_ = (crate::leanh::lean_unbox(v_lo_430_) as u8);
    v_hi_boxed_433_ = (crate::leanh::lean_unbox(v_hi_431_) as u8);
    v_res_434_ = l_UInt8_instHasSize__1___lam__0(v_lo_boxed_432_, v_hi_boxed_433_);
    return v_res_434_;
}
pub unsafe fn l_UInt8_instHasSize__2___lam__0(mut v_lo_437_: u8) -> *mut crate::leanh::LeanObject {
    let mut v___x_438_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_439_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_440_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_438_ = crate::leanh::lean_unsigned_to_nat(256);
    v___x_439_ = lean_uint8_to_nat(v_lo_437_);
    v___x_440_ = lean_nat_sub(v___x_438_, v___x_439_);
    return v___x_440_;
}
pub unsafe fn l_UInt8_instHasSize__2___lam__0___boxed(
    mut v_lo_441_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_lo_boxed_442_: u8 = 0;
    let mut v_res_443_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_lo_boxed_442_ = (crate::leanh::lean_unbox(v_lo_441_) as u8);
    v_res_443_ = l_UInt8_instHasSize__2___lam__0(v_lo_boxed_442_);
    return v_res_443_;
}
pub unsafe fn l_UInt16_instUpwardEnumerable___lam__0(
    mut v_i_446_: u16,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_447_: u16 = 0;
    let mut v___x_448_: u16 = 0;
    let mut v___x_449_: u16 = 0;
    let mut v___x_450_: u8 = 0;
    v___x_447_ = 1;
    v___x_448_ = lean_uint16_add(v_i_446_, v___x_447_);
    v___x_449_ = 0;
    v___x_450_ = lean_uint16_dec_eq(v___x_448_, v___x_449_);
    if v___x_450_ == 0 {
        let mut v___x_451_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_452_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_451_ = crate::leanh::lean_box((v___x_448_) as usize);
        v___x_452_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_452_, 0, v___x_451_);
        return v___x_452_;
    } else {
        let mut v___x_453_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_453_ = crate::leanh::lean_box(0);
        return v___x_453_;
    }
}
pub unsafe fn l_UInt16_instUpwardEnumerable___lam__0___boxed(
    mut v_i_454_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_i_boxed_455_: u16 = 0;
    let mut v_res_456_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_i_boxed_455_ = (crate::leanh::lean_unbox(v_i_454_) as u16);
    v_res_456_ = l_UInt16_instUpwardEnumerable___lam__0(v_i_boxed_455_);
    return v_res_456_;
}
pub unsafe fn l_UInt16_instUpwardEnumerable___lam__1(
    mut v_n_457_: *mut crate::leanh::LeanObject,
    mut v_i_458_: u16,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_459_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_460_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_461_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_462_: u8 = 0;
    v___x_459_ = lean_uint16_to_nat(v_i_458_);
    v___x_460_ = lean_nat_add(v___x_459_, v_n_457_);
    v___x_461_ = crate::leanh::lean_unsigned_to_nat(65536);
    v___x_462_ = lean_nat_dec_lt(v___x_460_, v___x_461_);
    if v___x_462_ == 0 {
        let mut v___x_463_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v___x_460_);
        v___x_463_ = crate::leanh::lean_box(0);
        return v___x_463_;
    } else {
        let mut v___x_464_: u16 = 0;
        let mut v___x_465_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_466_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_464_ = lean_uint16_of_nat(v___x_460_);
        crate::leanh::lean_dec(v___x_460_);
        v___x_465_ = crate::leanh::lean_box((v___x_464_) as usize);
        v___x_466_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_466_, 0, v___x_465_);
        return v___x_466_;
    }
}
pub unsafe fn l_UInt16_instUpwardEnumerable___lam__1___boxed(
    mut v_n_467_: *mut crate::leanh::LeanObject,
    mut v_i_468_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_i_boxed_469_: u16 = 0;
    let mut v_res_470_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_i_boxed_469_ = (crate::leanh::lean_unbox(v_i_468_) as u16);
    v_res_470_ = l_UInt16_instUpwardEnumerable___lam__1(v_n_467_, v_i_boxed_469_);
    crate::leanh::lean_dec(v_n_467_);
    return v_res_470_;
}
pub unsafe fn l_UInt16_instHasSize___lam__0(
    mut v_lo_481_: u16,
    mut v_hi_482_: u16,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_483_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_484_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_485_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_486_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_487_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_483_ = lean_uint16_to_nat(v_hi_482_);
    v___x_484_ = crate::leanh::lean_unsigned_to_nat(1);
    v___x_485_ = lean_nat_add(v___x_483_, v___x_484_);
    v___x_486_ = lean_uint16_to_nat(v_lo_481_);
    v___x_487_ = lean_nat_sub(v___x_485_, v___x_486_);
    crate::leanh::lean_dec(v___x_485_);
    return v___x_487_;
}
pub unsafe fn l_UInt16_instHasSize___lam__0___boxed(
    mut v_lo_488_: *mut crate::leanh::LeanObject,
    mut v_hi_489_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_lo_boxed_490_: u16 = 0;
    let mut v_hi_boxed_491_: u16 = 0;
    let mut v_res_492_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_lo_boxed_490_ = (crate::leanh::lean_unbox(v_lo_488_) as u16);
    v_hi_boxed_491_ = (crate::leanh::lean_unbox(v_hi_489_) as u16);
    v_res_492_ = l_UInt16_instHasSize___lam__0(v_lo_boxed_490_, v_hi_boxed_491_);
    return v_res_492_;
}
pub unsafe fn l_UInt16_instHasSize__1___lam__0(
    mut v_lo_495_: u16,
    mut v_hi_496_: u16,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_497_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_498_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_499_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_500_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_501_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_502_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_497_ = lean_uint16_to_nat(v_hi_496_);
    v___x_498_ = crate::leanh::lean_unsigned_to_nat(1);
    v___x_499_ = lean_nat_add(v___x_497_, v___x_498_);
    v___x_500_ = lean_uint16_to_nat(v_lo_495_);
    v___x_501_ = lean_nat_sub(v___x_499_, v___x_500_);
    crate::leanh::lean_dec(v___x_499_);
    v___x_502_ = lean_nat_sub(v___x_501_, v___x_498_);
    crate::leanh::lean_dec(v___x_501_);
    return v___x_502_;
}
pub unsafe fn l_UInt16_instHasSize__1___lam__0___boxed(
    mut v_lo_503_: *mut crate::leanh::LeanObject,
    mut v_hi_504_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_lo_boxed_505_: u16 = 0;
    let mut v_hi_boxed_506_: u16 = 0;
    let mut v_res_507_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_lo_boxed_505_ = (crate::leanh::lean_unbox(v_lo_503_) as u16);
    v_hi_boxed_506_ = (crate::leanh::lean_unbox(v_hi_504_) as u16);
    v_res_507_ = l_UInt16_instHasSize__1___lam__0(v_lo_boxed_505_, v_hi_boxed_506_);
    return v_res_507_;
}
pub unsafe fn l_UInt16_instHasSize__2___lam__0(
    mut v_lo_510_: u16,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_511_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_512_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_513_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_511_ = crate::leanh::lean_unsigned_to_nat(65536);
    v___x_512_ = lean_uint16_to_nat(v_lo_510_);
    v___x_513_ = lean_nat_sub(v___x_511_, v___x_512_);
    return v___x_513_;
}
pub unsafe fn l_UInt16_instHasSize__2___lam__0___boxed(
    mut v_lo_514_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_lo_boxed_515_: u16 = 0;
    let mut v_res_516_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_lo_boxed_515_ = (crate::leanh::lean_unbox(v_lo_514_) as u16);
    v_res_516_ = l_UInt16_instHasSize__2___lam__0(v_lo_boxed_515_);
    return v_res_516_;
}
pub unsafe fn l_UInt32_instUpwardEnumerable___lam__0(
    mut v_i_519_: u32,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_520_: u32 = 0;
    let mut v___x_521_: u32 = 0;
    let mut v___x_522_: u32 = 0;
    let mut v___x_523_: u8 = 0;
    v___x_520_ = 1;
    v___x_521_ = lean_uint32_add(v_i_519_, v___x_520_);
    v___x_522_ = 0;
    v___x_523_ = lean_uint32_dec_eq(v___x_521_, v___x_522_);
    if v___x_523_ == 0 {
        let mut v___x_524_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_525_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_524_ = crate::leanh::lean_box_uint32(v___x_521_);
        v___x_525_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_525_, 0, v___x_524_);
        return v___x_525_;
    } else {
        let mut v___x_526_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_526_ = crate::leanh::lean_box(0);
        return v___x_526_;
    }
}
pub unsafe fn l_UInt32_instUpwardEnumerable___lam__0___boxed(
    mut v_i_527_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_i_boxed_528_: u32 = 0;
    let mut v_res_529_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_i_boxed_528_ = crate::leanh::lean_unbox_uint32(v_i_527_);
    crate::leanh::lean_dec(v_i_527_);
    v_res_529_ = l_UInt32_instUpwardEnumerable___lam__0(v_i_boxed_528_);
    return v_res_529_;
}
pub unsafe fn l_UInt32_instUpwardEnumerable___lam__1(
    mut v_n_530_: *mut crate::leanh::LeanObject,
    mut v_i_531_: u32,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_532_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_533_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_534_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_535_: u8 = 0;
    v___x_532_ = lean_uint32_to_nat(v_i_531_);
    v___x_533_ = lean_nat_add(v___x_532_, v_n_530_);
    crate::leanh::lean_dec(v___x_532_);
    v___x_534_ = crate::leanh::lean_cstr_to_nat(b"4294967296\0".as_ptr().cast());
    v___x_535_ = lean_nat_dec_lt(v___x_533_, v___x_534_);
    if v___x_535_ == 0 {
        let mut v___x_536_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v___x_533_);
        v___x_536_ = crate::leanh::lean_box(0);
        return v___x_536_;
    } else {
        let mut v___x_537_: u32 = 0;
        let mut v___x_538_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_539_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_537_ = lean_uint32_of_nat(v___x_533_);
        crate::leanh::lean_dec(v___x_533_);
        v___x_538_ = crate::leanh::lean_box_uint32(v___x_537_);
        v___x_539_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_539_, 0, v___x_538_);
        return v___x_539_;
    }
}
pub unsafe fn l_UInt32_instUpwardEnumerable___lam__1___boxed(
    mut v_n_540_: *mut crate::leanh::LeanObject,
    mut v_i_541_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_i_boxed_542_: u32 = 0;
    let mut v_res_543_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_i_boxed_542_ = crate::leanh::lean_unbox_uint32(v_i_541_);
    crate::leanh::lean_dec(v_i_541_);
    v_res_543_ = l_UInt32_instUpwardEnumerable___lam__1(v_n_540_, v_i_boxed_542_);
    crate::leanh::lean_dec(v_n_540_);
    return v_res_543_;
}
pub unsafe fn _init_l_UInt32_instLeast_x3f___closed__0___boxed__const__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_550_: u32 = 0;
    let mut v___x_551_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_550_ = 0;
    v___x_551_ = crate::leanh::lean_box_uint32(v___x_550_);
    return v___x_551_;
}
pub unsafe fn _init_l_UInt32_instLeast_x3f___closed__0() -> *mut crate::leanh::LeanObject {
    let mut v___x_552_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_553_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_552_ = l_UInt32_instLeast_x3f___closed__0___boxed__const__1;
    v___x_553_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_553_, 0, v___x_552_);
    return v___x_553_;
}
pub unsafe fn _init_l_UInt32_instLeast_x3f() -> *mut crate::leanh::LeanObject {
    let mut v___x_554_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_554_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_UInt32_instLeast_x3f___closed__0),
        core::ptr::addr_of_mut!(l_UInt32_instLeast_x3f___closed__0_once),
        _init_l_UInt32_instLeast_x3f___closed__0,
    );
    return v___x_554_;
}
pub unsafe fn l_UInt32_instHasSize___lam__0(
    mut v_lo_555_: u32,
    mut v_hi_556_: u32,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_557_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_558_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_559_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_560_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_561_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_557_ = lean_uint32_to_nat(v_hi_556_);
    v___x_558_ = crate::leanh::lean_unsigned_to_nat(1);
    v___x_559_ = lean_nat_add(v___x_557_, v___x_558_);
    crate::leanh::lean_dec(v___x_557_);
    v___x_560_ = lean_uint32_to_nat(v_lo_555_);
    v___x_561_ = lean_nat_sub(v___x_559_, v___x_560_);
    crate::leanh::lean_dec(v___x_560_);
    crate::leanh::lean_dec(v___x_559_);
    return v___x_561_;
}
pub unsafe fn l_UInt32_instHasSize___lam__0___boxed(
    mut v_lo_562_: *mut crate::leanh::LeanObject,
    mut v_hi_563_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_lo_boxed_564_: u32 = 0;
    let mut v_hi_boxed_565_: u32 = 0;
    let mut v_res_566_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_lo_boxed_564_ = crate::leanh::lean_unbox_uint32(v_lo_562_);
    crate::leanh::lean_dec(v_lo_562_);
    v_hi_boxed_565_ = crate::leanh::lean_unbox_uint32(v_hi_563_);
    crate::leanh::lean_dec(v_hi_563_);
    v_res_566_ = l_UInt32_instHasSize___lam__0(v_lo_boxed_564_, v_hi_boxed_565_);
    return v_res_566_;
}
pub unsafe fn l_UInt32_instHasSize__1___lam__0(
    mut v_lo_569_: u32,
    mut v_hi_570_: u32,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_571_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_572_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_573_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_574_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_575_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_576_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_571_ = lean_uint32_to_nat(v_hi_570_);
    v___x_572_ = crate::leanh::lean_unsigned_to_nat(1);
    v___x_573_ = lean_nat_add(v___x_571_, v___x_572_);
    crate::leanh::lean_dec(v___x_571_);
    v___x_574_ = lean_uint32_to_nat(v_lo_569_);
    v___x_575_ = lean_nat_sub(v___x_573_, v___x_574_);
    crate::leanh::lean_dec(v___x_574_);
    crate::leanh::lean_dec(v___x_573_);
    v___x_576_ = lean_nat_sub(v___x_575_, v___x_572_);
    crate::leanh::lean_dec(v___x_575_);
    return v___x_576_;
}
pub unsafe fn l_UInt32_instHasSize__1___lam__0___boxed(
    mut v_lo_577_: *mut crate::leanh::LeanObject,
    mut v_hi_578_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_lo_boxed_579_: u32 = 0;
    let mut v_hi_boxed_580_: u32 = 0;
    let mut v_res_581_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_lo_boxed_579_ = crate::leanh::lean_unbox_uint32(v_lo_577_);
    crate::leanh::lean_dec(v_lo_577_);
    v_hi_boxed_580_ = crate::leanh::lean_unbox_uint32(v_hi_578_);
    crate::leanh::lean_dec(v_hi_578_);
    v_res_581_ = l_UInt32_instHasSize__1___lam__0(v_lo_boxed_579_, v_hi_boxed_580_);
    return v_res_581_;
}
pub unsafe fn l_UInt32_instHasSize__2___lam__0(
    mut v_lo_584_: u32,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_585_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_586_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_587_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_585_ = crate::leanh::lean_cstr_to_nat(b"4294967296\0".as_ptr().cast());
    v___x_586_ = lean_uint32_to_nat(v_lo_584_);
    v___x_587_ = lean_nat_sub(v___x_585_, v___x_586_);
    crate::leanh::lean_dec(v___x_586_);
    return v___x_587_;
}
pub unsafe fn l_UInt32_instHasSize__2___lam__0___boxed(
    mut v_lo_588_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_lo_boxed_589_: u32 = 0;
    let mut v_res_590_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_lo_boxed_589_ = crate::leanh::lean_unbox_uint32(v_lo_588_);
    crate::leanh::lean_dec(v_lo_588_);
    v_res_590_ = l_UInt32_instHasSize__2___lam__0(v_lo_boxed_589_);
    return v_res_590_;
}
pub unsafe fn l_UInt64_instUpwardEnumerable___lam__0(
    mut v_i_593_: u64,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_594_: u64 = 0;
    let mut v___x_595_: u64 = 0;
    let mut v___x_596_: u64 = 0;
    let mut v___x_597_: u8 = 0;
    v___x_594_ = 1u64;
    v___x_595_ = lean_uint64_add(v_i_593_, v___x_594_);
    v___x_596_ = 0u64;
    v___x_597_ = lean_uint64_dec_eq(v___x_595_, v___x_596_);
    if v___x_597_ == 0 {
        let mut v___x_598_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_599_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_598_ = crate::leanh::lean_box_uint64(v___x_595_);
        v___x_599_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_599_, 0, v___x_598_);
        return v___x_599_;
    } else {
        let mut v___x_600_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_600_ = crate::leanh::lean_box(0);
        return v___x_600_;
    }
}
pub unsafe fn l_UInt64_instUpwardEnumerable___lam__0___boxed(
    mut v_i_601_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_i_boxed_602_: u64 = 0;
    let mut v_res_603_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_i_boxed_602_ = crate::leanh::lean_unbox_uint64(v_i_601_);
    crate::leanh::lean_dec_ref(v_i_601_);
    v_res_603_ = l_UInt64_instUpwardEnumerable___lam__0(v_i_boxed_602_);
    return v_res_603_;
}
pub unsafe fn _init_l_UInt64_instUpwardEnumerable___lam__1___closed__0()
-> *mut crate::leanh::LeanObject {
    let mut v___x_604_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_604_ = crate::leanh::lean_cstr_to_nat(b"18446744073709551616\0".as_ptr().cast());
    return v___x_604_;
}
pub unsafe fn l_UInt64_instUpwardEnumerable___lam__1(
    mut v_n_605_: *mut crate::leanh::LeanObject,
    mut v_i_606_: u64,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_607_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_608_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_609_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_610_: u8 = 0;
    v___x_607_ = lean_uint64_to_nat(v_i_606_);
    v___x_608_ = lean_nat_add(v___x_607_, v_n_605_);
    crate::leanh::lean_dec(v___x_607_);
    v___x_609_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_UInt64_instUpwardEnumerable___lam__1___closed__0),
        core::ptr::addr_of_mut!(l_UInt64_instUpwardEnumerable___lam__1___closed__0_once),
        _init_l_UInt64_instUpwardEnumerable___lam__1___closed__0,
    );
    v___x_610_ = lean_nat_dec_lt(v___x_608_, v___x_609_);
    if v___x_610_ == 0 {
        let mut v___x_611_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v___x_608_);
        v___x_611_ = crate::leanh::lean_box(0);
        return v___x_611_;
    } else {
        let mut v___x_612_: u64 = 0;
        let mut v___x_613_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_614_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_612_ = lean_uint64_of_nat(v___x_608_);
        crate::leanh::lean_dec(v___x_608_);
        v___x_613_ = crate::leanh::lean_box_uint64(v___x_612_);
        v___x_614_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_614_, 0, v___x_613_);
        return v___x_614_;
    }
}
pub unsafe fn l_UInt64_instUpwardEnumerable___lam__1___boxed(
    mut v_n_615_: *mut crate::leanh::LeanObject,
    mut v_i_616_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_i_boxed_617_: u64 = 0;
    let mut v_res_618_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_i_boxed_617_ = crate::leanh::lean_unbox_uint64(v_i_616_);
    crate::leanh::lean_dec_ref(v_i_616_);
    v_res_618_ = l_UInt64_instUpwardEnumerable___lam__1(v_n_615_, v_i_boxed_617_);
    crate::leanh::lean_dec(v_n_615_);
    return v_res_618_;
}
pub unsafe fn l_UInt64_instHasSize___lam__0(
    mut v_lo_630_: u64,
    mut v_hi_631_: u64,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_632_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_633_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_634_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_635_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_636_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_632_ = lean_uint64_to_nat(v_hi_631_);
    v___x_633_ = crate::leanh::lean_unsigned_to_nat(1);
    v___x_634_ = lean_nat_add(v___x_632_, v___x_633_);
    crate::leanh::lean_dec(v___x_632_);
    v___x_635_ = lean_uint64_to_nat(v_lo_630_);
    v___x_636_ = lean_nat_sub(v___x_634_, v___x_635_);
    crate::leanh::lean_dec(v___x_635_);
    crate::leanh::lean_dec(v___x_634_);
    return v___x_636_;
}
pub unsafe fn l_UInt64_instHasSize___lam__0___boxed(
    mut v_lo_637_: *mut crate::leanh::LeanObject,
    mut v_hi_638_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_lo_boxed_639_: u64 = 0;
    let mut v_hi_boxed_640_: u64 = 0;
    let mut v_res_641_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_lo_boxed_639_ = crate::leanh::lean_unbox_uint64(v_lo_637_);
    crate::leanh::lean_dec_ref(v_lo_637_);
    v_hi_boxed_640_ = crate::leanh::lean_unbox_uint64(v_hi_638_);
    crate::leanh::lean_dec_ref(v_hi_638_);
    v_res_641_ = l_UInt64_instHasSize___lam__0(v_lo_boxed_639_, v_hi_boxed_640_);
    return v_res_641_;
}
pub unsafe fn l_UInt64_instHasSize__1___lam__0(
    mut v_lo_644_: u64,
    mut v_hi_645_: u64,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_646_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_647_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_648_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_649_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_650_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_651_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_646_ = lean_uint64_to_nat(v_hi_645_);
    v___x_647_ = crate::leanh::lean_unsigned_to_nat(1);
    v___x_648_ = lean_nat_add(v___x_646_, v___x_647_);
    crate::leanh::lean_dec(v___x_646_);
    v___x_649_ = lean_uint64_to_nat(v_lo_644_);
    v___x_650_ = lean_nat_sub(v___x_648_, v___x_649_);
    crate::leanh::lean_dec(v___x_649_);
    crate::leanh::lean_dec(v___x_648_);
    v___x_651_ = lean_nat_sub(v___x_650_, v___x_647_);
    crate::leanh::lean_dec(v___x_650_);
    return v___x_651_;
}
pub unsafe fn l_UInt64_instHasSize__1___lam__0___boxed(
    mut v_lo_652_: *mut crate::leanh::LeanObject,
    mut v_hi_653_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_lo_boxed_654_: u64 = 0;
    let mut v_hi_boxed_655_: u64 = 0;
    let mut v_res_656_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_lo_boxed_654_ = crate::leanh::lean_unbox_uint64(v_lo_652_);
    crate::leanh::lean_dec_ref(v_lo_652_);
    v_hi_boxed_655_ = crate::leanh::lean_unbox_uint64(v_hi_653_);
    crate::leanh::lean_dec_ref(v_hi_653_);
    v_res_656_ = l_UInt64_instHasSize__1___lam__0(v_lo_boxed_654_, v_hi_boxed_655_);
    return v_res_656_;
}
pub unsafe fn l_UInt64_instHasSize__2___lam__0(
    mut v_lo_659_: u64,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_660_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_661_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_662_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_660_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_UInt64_instUpwardEnumerable___lam__1___closed__0),
        core::ptr::addr_of_mut!(l_UInt64_instUpwardEnumerable___lam__1___closed__0_once),
        _init_l_UInt64_instUpwardEnumerable___lam__1___closed__0,
    );
    v___x_661_ = lean_uint64_to_nat(v_lo_659_);
    v___x_662_ = lean_nat_sub(v___x_660_, v___x_661_);
    crate::leanh::lean_dec(v___x_661_);
    return v___x_662_;
}
pub unsafe fn l_UInt64_instHasSize__2___lam__0___boxed(
    mut v_lo_663_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_lo_boxed_664_: u64 = 0;
    let mut v_res_665_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_lo_boxed_664_ = crate::leanh::lean_unbox_uint64(v_lo_663_);
    crate::leanh::lean_dec_ref(v_lo_663_);
    v_res_665_ = l_UInt64_instHasSize__2___lam__0(v_lo_boxed_664_);
    return v_res_665_;
}
pub unsafe fn l_USize_instUpwardEnumerable___lam__0(
    mut v_i_668_: usize,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_669_: usize = 0;
    let mut v___x_670_: usize = 0;
    let mut v___x_671_: usize = 0;
    let mut v___x_672_: u8 = 0;
    v___x_669_ = 1usize;
    v___x_670_ = lean_usize_add(v_i_668_, v___x_669_);
    v___x_671_ = 0usize;
    v___x_672_ = lean_usize_dec_eq(v___x_670_, v___x_671_);
    if v___x_672_ == 0 {
        let mut v___x_673_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_674_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_673_ = crate::leanh::lean_box_usize(v___x_670_);
        v___x_674_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_674_, 0, v___x_673_);
        return v___x_674_;
    } else {
        let mut v___x_675_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_675_ = crate::leanh::lean_box(0);
        return v___x_675_;
    }
}
pub unsafe fn l_USize_instUpwardEnumerable___lam__0___boxed(
    mut v_i_676_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_i_boxed_677_: usize = 0;
    let mut v_res_678_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_i_boxed_677_ = crate::leanh::lean_unbox_usize(v_i_676_);
    crate::leanh::lean_dec(v_i_676_);
    v_res_678_ = l_USize_instUpwardEnumerable___lam__0(v_i_boxed_677_);
    return v_res_678_;
}
pub unsafe fn _init_l_USize_instUpwardEnumerable___lam__1___closed__0()
-> *mut crate::leanh::LeanObject {
    let mut v___x_679_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_680_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_681_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_679_ = l_System_Platform_numBits;
    v___x_680_ = crate::leanh::lean_unsigned_to_nat(2);
    v___x_681_ = lean_nat_pow(v___x_680_, v___x_679_);
    return v___x_681_;
}
pub unsafe fn l_USize_instUpwardEnumerable___lam__1(
    mut v_n_682_: *mut crate::leanh::LeanObject,
    mut v_i_683_: usize,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_684_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_685_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_686_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_687_: u8 = 0;
    v___x_684_ = lean_usize_to_nat(v_i_683_);
    v___x_685_ = lean_nat_add(v___x_684_, v_n_682_);
    crate::leanh::lean_dec(v___x_684_);
    v___x_686_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_USize_instUpwardEnumerable___lam__1___closed__0),
        core::ptr::addr_of_mut!(l_USize_instUpwardEnumerable___lam__1___closed__0_once),
        _init_l_USize_instUpwardEnumerable___lam__1___closed__0,
    );
    v___x_687_ = lean_nat_dec_lt(v___x_685_, v___x_686_);
    if v___x_687_ == 0 {
        let mut v___x_688_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v___x_685_);
        v___x_688_ = crate::leanh::lean_box(0);
        return v___x_688_;
    } else {
        let mut v___x_689_: usize = 0;
        let mut v___x_690_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_691_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_689_ = lean_usize_of_nat(v___x_685_);
        crate::leanh::lean_dec(v___x_685_);
        v___x_690_ = crate::leanh::lean_box_usize(v___x_689_);
        v___x_691_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_691_, 0, v___x_690_);
        return v___x_691_;
    }
}
pub unsafe fn l_USize_instUpwardEnumerable___lam__1___boxed(
    mut v_n_692_: *mut crate::leanh::LeanObject,
    mut v_i_693_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_i_boxed_694_: usize = 0;
    let mut v_res_695_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_i_boxed_694_ = crate::leanh::lean_unbox_usize(v_i_693_);
    crate::leanh::lean_dec(v_i_693_);
    v_res_695_ = l_USize_instUpwardEnumerable___lam__1(v_n_692_, v_i_boxed_694_);
    crate::leanh::lean_dec(v_n_692_);
    return v_res_695_;
}
pub unsafe fn l_USize_instHasSize___lam__0(
    mut v_lo_707_: usize,
    mut v_hi_708_: usize,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_709_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_710_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_711_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_712_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_713_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_709_ = lean_usize_to_nat(v_hi_708_);
    v___x_710_ = crate::leanh::lean_unsigned_to_nat(1);
    v___x_711_ = lean_nat_add(v___x_709_, v___x_710_);
    crate::leanh::lean_dec(v___x_709_);
    v___x_712_ = lean_usize_to_nat(v_lo_707_);
    v___x_713_ = lean_nat_sub(v___x_711_, v___x_712_);
    crate::leanh::lean_dec(v___x_712_);
    crate::leanh::lean_dec(v___x_711_);
    return v___x_713_;
}
pub unsafe fn l_USize_instHasSize___lam__0___boxed(
    mut v_lo_714_: *mut crate::leanh::LeanObject,
    mut v_hi_715_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_lo_boxed_716_: usize = 0;
    let mut v_hi_boxed_717_: usize = 0;
    let mut v_res_718_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_lo_boxed_716_ = crate::leanh::lean_unbox_usize(v_lo_714_);
    crate::leanh::lean_dec(v_lo_714_);
    v_hi_boxed_717_ = crate::leanh::lean_unbox_usize(v_hi_715_);
    crate::leanh::lean_dec(v_hi_715_);
    v_res_718_ = l_USize_instHasSize___lam__0(v_lo_boxed_716_, v_hi_boxed_717_);
    return v_res_718_;
}
pub unsafe fn l_USize_instHasSize__1___lam__0(
    mut v_lo_721_: usize,
    mut v_hi_722_: usize,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_723_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_724_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_725_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_726_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_727_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_728_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_723_ = lean_usize_to_nat(v_hi_722_);
    v___x_724_ = crate::leanh::lean_unsigned_to_nat(1);
    v___x_725_ = lean_nat_add(v___x_723_, v___x_724_);
    crate::leanh::lean_dec(v___x_723_);
    v___x_726_ = lean_usize_to_nat(v_lo_721_);
    v___x_727_ = lean_nat_sub(v___x_725_, v___x_726_);
    crate::leanh::lean_dec(v___x_726_);
    crate::leanh::lean_dec(v___x_725_);
    v___x_728_ = lean_nat_sub(v___x_727_, v___x_724_);
    crate::leanh::lean_dec(v___x_727_);
    return v___x_728_;
}
pub unsafe fn l_USize_instHasSize__1___lam__0___boxed(
    mut v_lo_729_: *mut crate::leanh::LeanObject,
    mut v_hi_730_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_lo_boxed_731_: usize = 0;
    let mut v_hi_boxed_732_: usize = 0;
    let mut v_res_733_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_lo_boxed_731_ = crate::leanh::lean_unbox_usize(v_lo_729_);
    crate::leanh::lean_dec(v_lo_729_);
    v_hi_boxed_732_ = crate::leanh::lean_unbox_usize(v_hi_730_);
    crate::leanh::lean_dec(v_hi_730_);
    v_res_733_ = l_USize_instHasSize__1___lam__0(v_lo_boxed_731_, v_hi_boxed_732_);
    return v_res_733_;
}
pub unsafe fn l_USize_instHasSize__2___lam__0(
    mut v_lo_736_: usize,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_737_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_738_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_739_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_737_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_USize_instUpwardEnumerable___lam__1___closed__0),
        core::ptr::addr_of_mut!(l_USize_instUpwardEnumerable___lam__1___closed__0_once),
        _init_l_USize_instUpwardEnumerable___lam__1___closed__0,
    );
    v___x_738_ = lean_usize_to_nat(v_lo_736_);
    v___x_739_ = lean_nat_sub(v___x_737_, v___x_738_);
    crate::leanh::lean_dec(v___x_738_);
    return v___x_739_;
}
pub unsafe fn l_USize_instHasSize__2___lam__0___boxed(
    mut v_lo_740_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_lo_boxed_741_: usize = 0;
    let mut v_res_742_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_lo_boxed_741_ = crate::leanh::lean_unbox_usize(v_lo_740_);
    crate::leanh::lean_dec(v_lo_740_);
    v_res_742_ = l_USize_instHasSize__2___lam__0(v_lo_boxed_741_);
    return v_res_742_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Init_Data_Range_Polymorphic_UInt(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Init_Data_Range_Polymorphic_BitVec(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_UInt(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_ByCases(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_BitVec_Lemmas(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Option_Lemmas(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    l_UInt32_instLeast_x3f___closed__0___boxed__const__1 =
        _init_l_UInt32_instLeast_x3f___closed__0___boxed__const__1();
    crate::leanh::lean_mark_persistent(l_UInt32_instLeast_x3f___closed__0___boxed__const__1);
    l_UInt32_instLeast_x3f = _init_l_UInt32_instLeast_x3f();
    crate::leanh::lean_mark_persistent(l_UInt32_instLeast_x3f);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Init_Data_Range_Polymorphic_UInt(
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
pub unsafe fn initialize_Init_Data_Range_Polymorphic_UInt(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Init_Data_Range_Polymorphic_BitVec(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Data_UInt(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_ByCases(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Data_BitVec_Lemmas(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Data_Option_Lemmas(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Range_Polymorphic_UInt(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Init_Data_Range_Polymorphic_UInt(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Init_Data_Range_Polymorphic_UInt(builtin);
}
