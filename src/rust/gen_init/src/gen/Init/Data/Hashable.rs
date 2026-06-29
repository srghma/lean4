// Lean compiler output
// Module: Init.Data.Hashable
// Imports: Init.Data.Array.Basic Init.Data.UInt.Basic
use crate::r#gen::Init::Control::Id::{
    l_Id_instMonad___lam__0, l_Id_instMonad___lam__1___boxed, l_Id_instMonad___lam__2___boxed,
    l_Id_instMonad___lam__3, l_Id_instMonad___lam__4___boxed, l_Id_instMonad___lam__5___boxed,
    l_Id_instMonad___lam__6,
};
use crate::r#gen::Init::Data::Array::Basic::{
    initialize_Init_Data_Array_Basic, l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold,
    runtime_initialize_Init_Data_Array_Basic,
};
use crate::r#gen::Init::Data::UInt::Basic::{
    initialize_Init_Data_UInt_Basic, l_USize_toUInt64___boxed,
    runtime_initialize_Init_Data_UInt_Basic,
};
use crate::r#gen::Init::Data::UInt::BasicAux::{
    l_UInt8_toUInt64___boxed, l_UInt16_toUInt64___boxed, l_UInt32_toUInt64___boxed,
    l_UInt64_ofNat___boxed,
};
use crate::r#gen::Init::Prelude::l_List_foldl___redArg;
use crate::ffi::{
    lean_int_dec_lt, lean_nat_abs, lean_nat_to_int,
};
use crate::ffi::{lean_uint64_of_nat, lean_usize_of_nat};
use crate::ffi::{
    lean_array_get_size, lean_nat_add, lean_nat_dec_le, lean_nat_dec_lt, lean_nat_mul,
    lean_nat_sub, lean_uint64_mix_hash,
};
pub static l_instHashableNat___closed__0_value: crate::leanh::LeanClosureObject<0> =
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
        m_fun: l_UInt64_ofNat___boxed as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_instHashableNat___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_instHashableNat___closed__0_value) as *mut crate::leanh::LeanObject;
pub static mut l_instHashableNat: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_instHashableNat___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_instHashableBool___closed__0_value: crate::leanh::LeanClosureObject<0> =
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
        m_fun: l_instHashableBool___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_instHashableBool___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_instHashableBool___closed__0_value) as *mut crate::leanh::LeanObject;
pub static mut l_instHashableBool: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_instHashableBool___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_instHashablePEmpty___closed__0_value: crate::leanh::LeanClosureObject<0> =
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
        m_fun: l_instHashablePEmpty___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_instHashablePEmpty___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_instHashablePEmpty___closed__0_value) as *mut crate::leanh::LeanObject;
pub static mut l_instHashablePEmpty: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_instHashablePEmpty___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_instHashablePUnit___closed__0_value: crate::leanh::LeanClosureObject<0> =
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
        m_fun: l_instHashablePUnit___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_instHashablePUnit___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_instHashablePUnit___closed__0_value) as *mut crate::leanh::LeanObject;
pub static mut l_instHashablePUnit: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_instHashablePUnit___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_instHashableList___redArg___lam__1___boxed__const__1_value:
    crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 0
            + 8) as u16,
        other: 0,
        tag: 0,
    },
    m_objs: [7 as *mut crate::leanh::LeanObject],
};
pub static mut l_instHashableList___redArg___lam__1___boxed__const__1:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_instHashableList___redArg___lam__1___boxed__const__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_instHashableArray___redArg___lam__1___closed__0_value:
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
    m_fun: l_Id_instMonad___lam__0 as *const core::ffi::c_void,
    m_arity: 4,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_instHashableArray___redArg___lam__1___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_instHashableArray___redArg___lam__1___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_instHashableArray___redArg___lam__1___closed__1_value:
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
    m_fun: l_Id_instMonad___lam__1___boxed as *const core::ffi::c_void,
    m_arity: 4,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_instHashableArray___redArg___lam__1___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_instHashableArray___redArg___lam__1___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_instHashableArray___redArg___lam__1___closed__2_value:
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
    m_fun: l_Id_instMonad___lam__2___boxed as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_instHashableArray___redArg___lam__1___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_instHashableArray___redArg___lam__1___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l_instHashableArray___redArg___lam__1___closed__3_value:
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
    m_fun: l_Id_instMonad___lam__3 as *const core::ffi::c_void,
    m_arity: 4,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_instHashableArray___redArg___lam__1___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_instHashableArray___redArg___lam__1___closed__3_value)
        as *mut crate::leanh::LeanObject;
pub static l_instHashableArray___redArg___lam__1___closed__4_value:
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
    m_fun: l_Id_instMonad___lam__4___boxed as *const core::ffi::c_void,
    m_arity: 4,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_instHashableArray___redArg___lam__1___closed__4: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_instHashableArray___redArg___lam__1___closed__4_value)
        as *mut crate::leanh::LeanObject;
pub static l_instHashableArray___redArg___lam__1___closed__5_value:
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
    m_fun: l_Id_instMonad___lam__5___boxed as *const core::ffi::c_void,
    m_arity: 4,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_instHashableArray___redArg___lam__1___closed__5: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_instHashableArray___redArg___lam__1___closed__5_value)
        as *mut crate::leanh::LeanObject;
pub static l_instHashableArray___redArg___lam__1___closed__6_value:
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
    m_fun: l_Id_instMonad___lam__6 as *const core::ffi::c_void,
    m_arity: 4,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_instHashableArray___redArg___lam__1___closed__6: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_instHashableArray___redArg___lam__1___closed__6_value)
        as *mut crate::leanh::LeanObject;
pub static l_instHashableArray___redArg___lam__1___closed__7_value: crate::leanh::LeanCtorObject<
    2,
> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 0,
    },
    m_objs: [
        core::ptr::addr_of!(l_instHashableArray___redArg___lam__1___closed__0_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_instHashableArray___redArg___lam__1___closed__1_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_instHashableArray___redArg___lam__1___closed__7: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_instHashableArray___redArg___lam__1___closed__7_value)
        as *mut crate::leanh::LeanObject;
pub static l_instHashableArray___redArg___lam__1___closed__8_value: crate::leanh::LeanCtorObject<
    5,
> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 5
            + 0) as u16,
        other: 5,
        tag: 0,
    },
    m_objs: [
        core::ptr::addr_of!(l_instHashableArray___redArg___lam__1___closed__7_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_instHashableArray___redArg___lam__1___closed__2_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_instHashableArray___redArg___lam__1___closed__3_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_instHashableArray___redArg___lam__1___closed__4_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_instHashableArray___redArg___lam__1___closed__5_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_instHashableArray___redArg___lam__1___closed__8: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_instHashableArray___redArg___lam__1___closed__8_value)
        as *mut crate::leanh::LeanObject;
pub static l_instHashableArray___redArg___lam__1___closed__9_value: crate::leanh::LeanCtorObject<
    2,
> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 0,
    },
    m_objs: [
        core::ptr::addr_of!(l_instHashableArray___redArg___lam__1___closed__8_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_instHashableArray___redArg___lam__1___closed__6_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_instHashableArray___redArg___lam__1___closed__9: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_instHashableArray___redArg___lam__1___closed__9_value)
        as *mut crate::leanh::LeanObject;
pub static l_instHashableUInt8___closed__0_value: crate::leanh::LeanClosureObject<0> =
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
        m_fun: l_UInt8_toUInt64___boxed as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_instHashableUInt8___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_instHashableUInt8___closed__0_value) as *mut crate::leanh::LeanObject;
pub static mut l_instHashableUInt8: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_instHashableUInt8___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_instHashableUInt16___closed__0_value: crate::leanh::LeanClosureObject<0> =
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
        m_fun: l_UInt16_toUInt64___boxed as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_instHashableUInt16___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_instHashableUInt16___closed__0_value) as *mut crate::leanh::LeanObject;
pub static mut l_instHashableUInt16: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_instHashableUInt16___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_instHashableUInt32___closed__0_value: crate::leanh::LeanClosureObject<0> =
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
        m_fun: l_UInt32_toUInt64___boxed as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_instHashableUInt32___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_instHashableUInt32___closed__0_value) as *mut crate::leanh::LeanObject;
pub static mut l_instHashableUInt32: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_instHashableUInt32___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_instHashableUInt64___closed__0_value: crate::leanh::LeanClosureObject<0> =
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
        m_fun: l_instHashableUInt64___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_instHashableUInt64___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_instHashableUInt64___closed__0_value) as *mut crate::leanh::LeanObject;
pub static mut l_instHashableUInt64: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_instHashableUInt64___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_instHashableUSize___closed__0_value: crate::leanh::LeanClosureObject<0> =
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
        m_fun: l_USize_toUInt64___boxed as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_instHashableUSize___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_instHashableUSize___closed__0_value) as *mut crate::leanh::LeanObject;
pub static mut l_instHashableUSize: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_instHashableUSize___closed__0_value) as *mut crate::leanh::LeanObject;
pub static mut l_instHashableChar: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_instHashableUInt32___closed__0_value) as *mut crate::leanh::LeanObject;
static mut l_instHashableInt___lam__0___closed__0_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_instHashableInt___lam__0___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_instHashableInt___closed__0_value: crate::leanh::LeanClosureObject<0> =
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
        m_fun: l_instHashableInt___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_instHashableInt___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_instHashableInt___closed__0_value) as *mut crate::leanh::LeanObject;
pub static mut l_instHashableInt: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_instHashableInt___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_instHashable___closed__0_value: crate::leanh::LeanClosureObject<0> =
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
        m_fun: l_instHashable___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_instHashable___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_instHashable___closed__0_value) as *mut crate::leanh::LeanObject;
pub unsafe fn l_instHashableProd___redArg___lam__0(
    mut v_inst_212_: *mut crate::leanh::LeanObject,
    mut v_inst_213_: *mut crate::leanh::LeanObject,
    mut v_x_214_: *mut crate::leanh::LeanObject,
) -> u64 {
    let mut v_fst_215_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_216_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_217_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_218_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_219_: u64 = 0;
    let mut v___x_220_: u64 = 0;
    let mut v___x_221_: u64 = 0;
    v_fst_215_ = crate::leanh::lean_ctor_get(v_x_214_, 0);
    crate::leanh::lean_inc(v_fst_215_);
    v_snd_216_ = crate::leanh::lean_ctor_get(v_x_214_, 1);
    crate::leanh::lean_inc(v_snd_216_);
    crate::leanh::lean_dec_ref(v_x_214_);
    v___x_217_ = crate::leanh::lean_apply_1(v_inst_212_, v_fst_215_);
    v___x_218_ = crate::leanh::lean_apply_1(v_inst_213_, v_snd_216_);
    v___x_219_ = crate::leanh::lean_unbox_uint64(v___x_217_);
    crate::leanh::lean_dec_ref(v___x_217_);
    v___x_220_ = crate::leanh::lean_unbox_uint64(v___x_218_);
    crate::leanh::lean_dec_ref(v___x_218_);
    v___x_221_ = lean_uint64_mix_hash(v___x_219_, v___x_220_);
    return v___x_221_;
}
pub unsafe fn l_instHashableProd___redArg___lam__0___boxed(
    mut v_inst_222_: *mut crate::leanh::LeanObject,
    mut v_inst_223_: *mut crate::leanh::LeanObject,
    mut v_x_224_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_225_: u64 = 0;
    let mut v_r_226_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_225_ = l_instHashableProd___redArg___lam__0(v_inst_222_, v_inst_223_, v_x_224_);
    v_r_226_ = crate::leanh::lean_box_uint64(v_res_225_);
    return v_r_226_;
}
pub unsafe fn l_instHashableProd___redArg(
    mut v_inst_227_: *mut crate::leanh::LeanObject,
    mut v_inst_228_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_229_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_229_ = crate::leanh::lean_alloc_closure(
        l_instHashableProd___redArg___lam__0___boxed as *mut core::ffi::c_void,
        3,
        2,
    );
    crate::leanh::lean_closure_set(v___f_229_, 0, v_inst_227_);
    crate::leanh::lean_closure_set(v___f_229_, 1, v_inst_228_);
    return v___f_229_;
}
pub unsafe fn l_instHashableProd(
    mut v_00_u03b1_230_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_231_: *mut crate::leanh::LeanObject,
    mut v_inst_232_: *mut crate::leanh::LeanObject,
    mut v_inst_233_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_234_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_234_ = crate::leanh::lean_alloc_closure(
        l_instHashableProd___redArg___lam__0___boxed as *mut core::ffi::c_void,
        3,
        2,
    );
    crate::leanh::lean_closure_set(v___f_234_, 0, v_inst_232_);
    crate::leanh::lean_closure_set(v___f_234_, 1, v_inst_233_);
    return v___f_234_;
}
pub unsafe fn l_instHashableBool___lam__0(mut v_x_235_: u8) -> u64 {
    if v_x_235_ == 0 {
        let mut v___x_236_: u64 = 0;
        v___x_236_ = 13u64;
        return v___x_236_;
    } else {
        let mut v___x_237_: u64 = 0;
        v___x_237_ = 11u64;
        return v___x_237_;
    }
}
pub unsafe fn l_instHashableBool___lam__0___boxed(
    mut v_x_238_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_x_32__boxed_239_: u8 = 0;
    let mut v_res_240_: u64 = 0;
    let mut v_r_241_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_x_32__boxed_239_ = (crate::leanh::lean_unbox(v_x_238_) as u8);
    v_res_240_ = l_instHashableBool___lam__0(v_x_32__boxed_239_);
    v_r_241_ = crate::leanh::lean_box_uint64(v_res_240_);
    return v_r_241_;
}
pub unsafe fn l_instHashablePEmpty___lam__0(mut v_x_244_: u8) -> u64 {
    core::hint::unreachable_unchecked();
}
pub unsafe fn l_instHashablePEmpty___lam__0___boxed(
    mut v_x_245_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_x_boxed_246_: u8 = 0;
    let mut v_res_247_: u64 = 0;
    let mut v_r_248_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_x_boxed_246_ = (crate::leanh::lean_unbox(v_x_245_) as u8);
    v_res_247_ = l_instHashablePEmpty___lam__0(v_x_boxed_246_);
    v_r_248_ = crate::leanh::lean_box_uint64(v_res_247_);
    return v_r_248_;
}
pub unsafe fn l_instHashablePUnit___lam__0(mut v_x_251_: *mut crate::leanh::LeanObject) -> u64 {
    let mut v___x_252_: u64 = 0;
    v___x_252_ = 11u64;
    return v___x_252_;
}
pub unsafe fn l_instHashablePUnit___lam__0___boxed(
    mut v_x_253_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_254_: u64 = 0;
    let mut v_r_255_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_254_ = l_instHashablePUnit___lam__0(v_x_253_);
    v_r_255_ = crate::leanh::lean_box_uint64(v_res_254_);
    return v_r_255_;
}
pub unsafe fn l_instHashableOption___redArg___lam__0(
    mut v_inst_258_: *mut crate::leanh::LeanObject,
    mut v_x_259_: *mut crate::leanh::LeanObject,
) -> u64 {
    if crate::leanh::lean_obj_tag(v_x_259_) == 0 {
        let mut v___x_260_: u64 = 0;
        crate::leanh::lean_dec_ref(v_inst_258_);
        v___x_260_ = 11u64;
        return v___x_260_;
    } else {
        let mut v_val_261_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_262_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_263_: u64 = 0;
        let mut v___x_264_: u64 = 0;
        let mut v___x_265_: u64 = 0;
        v_val_261_ = crate::leanh::lean_ctor_get(v_x_259_, 0);
        crate::leanh::lean_inc(v_val_261_);
        crate::leanh::lean_dec_ref_known(v_x_259_, 1);
        v___x_262_ = crate::leanh::lean_apply_1(v_inst_258_, v_val_261_);
        v___x_263_ = 13u64;
        v___x_264_ = crate::leanh::lean_unbox_uint64(v___x_262_);
        crate::leanh::lean_dec_ref(v___x_262_);
        v___x_265_ = lean_uint64_mix_hash(v___x_264_, v___x_263_);
        return v___x_265_;
    }
}
pub unsafe fn l_instHashableOption___redArg___lam__0___boxed(
    mut v_inst_266_: *mut crate::leanh::LeanObject,
    mut v_x_267_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_268_: u64 = 0;
    let mut v_r_269_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_268_ = l_instHashableOption___redArg___lam__0(v_inst_266_, v_x_267_);
    v_r_269_ = crate::leanh::lean_box_uint64(v_res_268_);
    return v_r_269_;
}
pub unsafe fn l_instHashableOption___redArg(
    mut v_inst_270_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_271_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_271_ = crate::leanh::lean_alloc_closure(
        l_instHashableOption___redArg___lam__0___boxed as *mut core::ffi::c_void,
        2,
        1,
    );
    crate::leanh::lean_closure_set(v___f_271_, 0, v_inst_270_);
    return v___f_271_;
}
pub unsafe fn l_instHashableOption(
    mut v_00_u03b1_272_: *mut crate::leanh::LeanObject,
    mut v_inst_273_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_274_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_274_ = crate::leanh::lean_alloc_closure(
        l_instHashableOption___redArg___lam__0___boxed as *mut core::ffi::c_void,
        2,
        1,
    );
    crate::leanh::lean_closure_set(v___f_274_, 0, v_inst_273_);
    return v___f_274_;
}
pub unsafe fn l_instHashableList___redArg___lam__0(
    mut v_inst_275_: *mut crate::leanh::LeanObject,
    mut v_r_276_: u64,
    mut v_a_277_: *mut crate::leanh::LeanObject,
) -> u64 {
    let mut v___x_278_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_279_: u64 = 0;
    let mut v___x_280_: u64 = 0;
    v___x_278_ = crate::leanh::lean_apply_1(v_inst_275_, v_a_277_);
    v___x_279_ = crate::leanh::lean_unbox_uint64(v___x_278_);
    crate::leanh::lean_dec_ref(v___x_278_);
    v___x_280_ = lean_uint64_mix_hash(v_r_276_, v___x_279_);
    return v___x_280_;
}
pub unsafe fn l_instHashableList___redArg___lam__0___boxed(
    mut v_inst_281_: *mut crate::leanh::LeanObject,
    mut v_r_282_: *mut crate::leanh::LeanObject,
    mut v_a_283_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_r_boxed_284_: u64 = 0;
    let mut v_res_285_: u64 = 0;
    let mut v_r_286_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_r_boxed_284_ = crate::leanh::lean_unbox_uint64(v_r_282_);
    crate::leanh::lean_dec_ref(v_r_282_);
    v_res_285_ = l_instHashableList___redArg___lam__0(v_inst_281_, v_r_boxed_284_, v_a_283_);
    v_r_286_ = crate::leanh::lean_box_uint64(v_res_285_);
    return v_r_286_;
}
pub unsafe fn l_instHashableList___redArg___lam__1(
    mut v___f_289_: *mut crate::leanh::LeanObject,
    mut v_as_290_: *mut crate::leanh::LeanObject,
) -> u64 {
    let mut v___x_291_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_292_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_293_: u64 = 0;
    v___x_291_ = l_instHashableList___redArg___lam__1___boxed__const__1;
    v___x_292_ = l_List_foldl___redArg(v___f_289_, v___x_291_, v_as_290_);
    v___x_293_ = crate::leanh::lean_unbox_uint64(v___x_292_);
    crate::leanh::lean_dec(v___x_292_);
    return v___x_293_;
}
pub unsafe fn l_instHashableList___redArg___lam__1___boxed(
    mut v___f_294_: *mut crate::leanh::LeanObject,
    mut v_as_295_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_296_: u64 = 0;
    let mut v_r_297_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_296_ = l_instHashableList___redArg___lam__1(v___f_294_, v_as_295_);
    v_r_297_ = crate::leanh::lean_box_uint64(v_res_296_);
    return v_r_297_;
}
pub unsafe fn l_instHashableList___redArg(
    mut v_inst_298_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_299_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_300_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_299_ = crate::leanh::lean_alloc_closure(
        l_instHashableList___redArg___lam__0___boxed as *mut core::ffi::c_void,
        3,
        1,
    );
    crate::leanh::lean_closure_set(v___f_299_, 0, v_inst_298_);
    v___f_300_ = crate::leanh::lean_alloc_closure(
        l_instHashableList___redArg___lam__1___boxed as *mut core::ffi::c_void,
        2,
        1,
    );
    crate::leanh::lean_closure_set(v___f_300_, 0, v___f_299_);
    return v___f_300_;
}
pub unsafe fn l_instHashableList(
    mut v_00_u03b1_301_: *mut crate::leanh::LeanObject,
    mut v_inst_302_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_303_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_303_ = l_instHashableList___redArg(v_inst_302_);
    return v___x_303_;
}
pub unsafe fn l_instHashableArray___redArg___lam__0(
    mut v_inst_304_: *mut crate::leanh::LeanObject,
    mut v_x1_305_: u64,
    mut v_x2_306_: *mut crate::leanh::LeanObject,
) -> u64 {
    let mut v___x_307_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_308_: u64 = 0;
    let mut v___x_309_: u64 = 0;
    v___x_307_ = crate::leanh::lean_apply_1(v_inst_304_, v_x2_306_);
    v___x_308_ = crate::leanh::lean_unbox_uint64(v___x_307_);
    crate::leanh::lean_dec_ref(v___x_307_);
    v___x_309_ = lean_uint64_mix_hash(v_x1_305_, v___x_308_);
    return v___x_309_;
}
pub unsafe fn l_instHashableArray___redArg___lam__0___boxed(
    mut v_inst_310_: *mut crate::leanh::LeanObject,
    mut v_x1_311_: *mut crate::leanh::LeanObject,
    mut v_x2_312_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_x1_84__boxed_313_: u64 = 0;
    let mut v_res_314_: u64 = 0;
    let mut v_r_315_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_x1_84__boxed_313_ = crate::leanh::lean_unbox_uint64(v_x1_311_);
    crate::leanh::lean_dec_ref(v_x1_311_);
    v_res_314_ = l_instHashableArray___redArg___lam__0(v_inst_310_, v_x1_84__boxed_313_, v_x2_312_);
    v_r_315_ = crate::leanh::lean_box_uint64(v_res_314_);
    return v_r_315_;
}
pub unsafe fn l_instHashableArray___redArg___lam__1(
    mut v___f_335_: *mut crate::leanh::LeanObject,
    mut v_as_336_: *mut crate::leanh::LeanObject,
) -> u64 {
    let mut v___x_337_: u64 = 0;
    let mut v___x_338_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_339_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_340_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_341_: u8 = 0;
    v___x_337_ = 7u64;
    v___x_338_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_339_ = lean_array_get_size(v_as_336_);
    v___x_340_ = l_instHashableArray___redArg___lam__1___closed__9;
    v___x_341_ = lean_nat_dec_lt(v___x_338_, v___x_339_);
    if v___x_341_ == 0 {
        crate::leanh::lean_dec_ref(v_as_336_);
        crate::leanh::lean_dec_ref(v___f_335_);
        return v___x_337_;
    } else {
        let mut v___x_342_: u8 = 0;
        v___x_342_ = lean_nat_dec_le(v___x_339_, v___x_339_);
        if v___x_342_ == 0 {
            if v___x_341_ == 0 {
                crate::leanh::lean_dec_ref(v_as_336_);
                crate::leanh::lean_dec_ref(v___f_335_);
                return v___x_337_;
            } else {
                let mut v___x_343_: usize = 0;
                let mut v___x_344_: usize = 0;
                let mut v___x_345_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_346_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_347_: u64 = 0;
                v___x_343_ = 0usize;
                v___x_344_ = lean_usize_of_nat(v___x_339_);
                v___x_345_ = l_instHashableList___redArg___lam__1___boxed__const__1;
                v___x_346_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(
                    crate::leanh::lean_box(0),
                    crate::leanh::lean_box(0),
                    crate::leanh::lean_box(0),
                    v___x_340_,
                    v___f_335_,
                    v_as_336_,
                    v___x_343_,
                    v___x_344_,
                    v___x_345_,
                );
                v___x_347_ = crate::leanh::lean_unbox_uint64(v___x_346_);
                crate::leanh::lean_dec(v___x_346_);
                return v___x_347_;
            }
        } else {
            let mut v___x_348_: usize = 0;
            let mut v___x_349_: usize = 0;
            let mut v___x_350_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_351_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_352_: u64 = 0;
            v___x_348_ = 0usize;
            v___x_349_ = lean_usize_of_nat(v___x_339_);
            v___x_350_ = l_instHashableList___redArg___lam__1___boxed__const__1;
            v___x_351_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(
                crate::leanh::lean_box(0),
                crate::leanh::lean_box(0),
                crate::leanh::lean_box(0),
                v___x_340_,
                v___f_335_,
                v_as_336_,
                v___x_348_,
                v___x_349_,
                v___x_350_,
            );
            v___x_352_ = crate::leanh::lean_unbox_uint64(v___x_351_);
            crate::leanh::lean_dec(v___x_351_);
            return v___x_352_;
        }
    }
}
pub unsafe fn l_instHashableArray___redArg___lam__1___boxed(
    mut v___f_353_: *mut crate::leanh::LeanObject,
    mut v_as_354_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_355_: u64 = 0;
    let mut v_r_356_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_355_ = l_instHashableArray___redArg___lam__1(v___f_353_, v_as_354_);
    v_r_356_ = crate::leanh::lean_box_uint64(v_res_355_);
    return v_r_356_;
}
pub unsafe fn l_instHashableArray___redArg(
    mut v_inst_357_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_358_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_359_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_358_ = crate::leanh::lean_alloc_closure(
        l_instHashableArray___redArg___lam__0___boxed as *mut core::ffi::c_void,
        3,
        1,
    );
    crate::leanh::lean_closure_set(v___f_358_, 0, v_inst_357_);
    v___f_359_ = crate::leanh::lean_alloc_closure(
        l_instHashableArray___redArg___lam__1___boxed as *mut core::ffi::c_void,
        2,
        1,
    );
    crate::leanh::lean_closure_set(v___f_359_, 0, v___f_358_);
    return v___f_359_;
}
pub unsafe fn l_instHashableArray(
    mut v_00_u03b1_360_: *mut crate::leanh::LeanObject,
    mut v_inst_361_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_362_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_362_ = l_instHashableArray___redArg(v_inst_361_);
    return v___x_362_;
}
pub unsafe fn l_instHashableUInt64___lam__0(mut v_n_369_: u64) -> u64 {
    return v_n_369_;
}
pub unsafe fn l_instHashableUInt64___lam__0___boxed(
    mut v_n_370_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_n_boxed_371_: u64 = 0;
    let mut v_res_372_: u64 = 0;
    let mut v_r_373_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_n_boxed_371_ = crate::leanh::lean_unbox_uint64(v_n_370_);
    crate::leanh::lean_dec_ref(v_n_370_);
    v_res_372_ = l_instHashableUInt64___lam__0(v_n_boxed_371_);
    v_r_373_ = crate::leanh::lean_box_uint64(v_res_372_);
    return v_r_373_;
}
pub unsafe fn l_instHashableFin(
    mut v_n_378_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_379_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_379_ = l_instHashableNat___closed__0;
    return v___f_379_;
}
pub unsafe fn l_instHashableFin___boxed(
    mut v_n_380_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_381_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_381_ = l_instHashableFin(v_n_380_);
    crate::leanh::lean_dec(v_n_380_);
    return v_res_381_;
}
pub unsafe fn _init_l_instHashableInt___lam__0___closed__0() -> *mut crate::leanh::LeanObject {
    let mut v_natZero_383_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_intZero_384_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_natZero_383_ = crate::leanh::lean_unsigned_to_nat(0);
    v_intZero_384_ = lean_nat_to_int(v_natZero_383_);
    return v_intZero_384_;
}
pub unsafe fn l_instHashableInt___lam__0(mut v_x_385_: *mut crate::leanh::LeanObject) -> u64 {
    let mut v_intZero_386_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isNeg_387_: u8 = 0;
    v_intZero_386_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_instHashableInt___lam__0___closed__0),
        core::ptr::addr_of_mut!(l_instHashableInt___lam__0___closed__0_once),
        _init_l_instHashableInt___lam__0___closed__0,
    );
    v_isNeg_387_ = lean_int_dec_lt(v_x_385_, v_intZero_386_);
    if v_isNeg_387_ == 0 {
        let mut v_a_388_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_389_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_390_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_391_: u64 = 0;
        v_a_388_ = lean_nat_abs(v_x_385_);
        v___x_389_ = crate::leanh::lean_unsigned_to_nat(2);
        v___x_390_ = lean_nat_mul(v___x_389_, v_a_388_);
        crate::leanh::lean_dec(v_a_388_);
        v___x_391_ = lean_uint64_of_nat(v___x_390_);
        crate::leanh::lean_dec(v___x_390_);
        return v___x_391_;
    } else {
        let mut v_abs_392_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_one_393_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_a_394_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_395_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_396_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_397_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_398_: u64 = 0;
        v_abs_392_ = lean_nat_abs(v_x_385_);
        v_one_393_ = crate::leanh::lean_unsigned_to_nat(1);
        v_a_394_ = lean_nat_sub(v_abs_392_, v_one_393_);
        crate::leanh::lean_dec(v_abs_392_);
        v___x_395_ = crate::leanh::lean_unsigned_to_nat(2);
        v___x_396_ = lean_nat_mul(v___x_395_, v_a_394_);
        crate::leanh::lean_dec(v_a_394_);
        v___x_397_ = lean_nat_add(v___x_396_, v_one_393_);
        crate::leanh::lean_dec(v___x_396_);
        v___x_398_ = lean_uint64_of_nat(v___x_397_);
        crate::leanh::lean_dec(v___x_397_);
        return v___x_398_;
    }
}
pub unsafe fn l_instHashableInt___lam__0___boxed(
    mut v_x_399_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_400_: u64 = 0;
    let mut v_r_401_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_400_ = l_instHashableInt___lam__0(v_x_399_);
    crate::leanh::lean_dec(v_x_399_);
    v_r_401_ = crate::leanh::lean_box_uint64(v_res_400_);
    return v_r_401_;
}
pub unsafe fn l_instHashable___lam__0(mut v_x_404_: *mut crate::leanh::LeanObject) -> u64 {
    let mut v___x_405_: u64 = 0;
    v___x_405_ = 0u64;
    return v___x_405_;
}
pub unsafe fn l_instHashable___lam__0___boxed(
    mut v_x_406_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_407_: u64 = 0;
    let mut v_r_408_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_407_ = l_instHashable___lam__0(v_x_406_);
    v_r_408_ = crate::leanh::lean_box_uint64(v_res_407_);
    return v_r_408_;
}
pub unsafe fn l_instHashable(
    mut v_P_410_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_411_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_411_ = l_instHashable___closed__0;
    return v___f_411_;
}
pub unsafe fn l_hash64(mut v_u_412_: u64) -> u64 {
    let mut v___x_413_: u64 = 0;
    let mut v___x_414_: u64 = 0;
    v___x_413_ = 11u64;
    v___x_414_ = lean_uint64_mix_hash(v_u_412_, v___x_413_);
    return v___x_414_;
}
pub unsafe fn l_hash64___boxed(
    mut v_u_415_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_u_boxed_416_: u64 = 0;
    let mut v_res_417_: u64 = 0;
    let mut v_r_418_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_u_boxed_416_ = crate::leanh::lean_unbox_uint64(v_u_415_);
    crate::leanh::lean_dec_ref(v_u_415_);
    v_res_417_ = l_hash64(v_u_boxed_416_);
    v_r_418_ = crate::leanh::lean_box_uint64(v_res_417_);
    return v_r_418_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Init_Data_Hashable(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Init_Data_Array_Basic(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_UInt_Basic(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Init_Data_Hashable(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_meta_initialized = true;
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Init_Data_Hashable(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Init_Data_Array_Basic(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Data_UInt_Basic(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Hashable(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Init_Data_Hashable(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Init_Data_Hashable(builtin);
}
