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
use crate::lean_imports_rs::Init::Data::UInt::Basic::{
    lean_uint8_add, lean_uint16_add, lean_uint64_add,
};
use crate::lean_imports_rs::Init::Data::UInt::BasicAux::{
    lean_uint8_to_nat, lean_uint16_to_nat, lean_uint32_add, lean_uint64_to_nat, lean_usize_add,
    lean_usize_to_nat,
};
use crate::lean_imports_rs::Init::Prelude::{
    lean_nat_add, lean_nat_dec_lt, lean_nat_pow, lean_nat_sub, lean_uint8_dec_eq,
    lean_uint8_of_nat, lean_uint16_dec_eq, lean_uint16_of_nat, lean_uint32_dec_eq,
    lean_uint32_of_nat, lean_uint32_to_nat, lean_uint64_dec_eq, lean_uint64_of_nat,
    lean_usize_dec_eq, lean_usize_of_nat,
};
use crate::leanh::{
    LeanArrayObject, LeanClosureObject, LeanCtorObject, LeanExternalClass, LeanExternalObject,
    LeanObject, LeanOnceCell, LeanPromiseObject, LeanRefObject, LeanScalarArray, LeanStringObject,
    LeanTaskObject, LeanThunkObject, lean_alloc_ctor, lean_box, lean_box_uint32, lean_box_uint64,
    lean_box_usize, lean_cstr_to_nat, lean_ctor_set, lean_dec, lean_dec_ref,
    lean_io_result_is_error, lean_io_result_mk_ok, lean_mark_persistent, lean_obj_once, lean_unbox,
    lean_unbox_uint32, lean_unbox_uint64, lean_unbox_usize, lean_unsigned_to_nat,
};
pub static l_UInt8_instUpwardEnumerable___closed__0_value: LeanClosureObject<0> =
    LeanClosureObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_UInt8_instUpwardEnumerable___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_UInt8_instUpwardEnumerable___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_UInt8_instUpwardEnumerable___closed__0_value) as *mut LeanObject;
pub static l_UInt8_instUpwardEnumerable___closed__1_value: LeanClosureObject<0> =
    LeanClosureObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_UInt8_instUpwardEnumerable___lam__1___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_UInt8_instUpwardEnumerable___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_UInt8_instUpwardEnumerable___closed__1_value) as *mut LeanObject;
pub static l_UInt8_instUpwardEnumerable___closed__2_value: LeanCtorObject<2> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 0,
    },
    m_objs: [
        core::ptr::addr_of!(l_UInt8_instUpwardEnumerable___closed__0_value) as *mut LeanObject,
        core::ptr::addr_of!(l_UInt8_instUpwardEnumerable___closed__1_value) as *mut LeanObject,
    ],
};
static mut l_UInt8_instUpwardEnumerable___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_UInt8_instUpwardEnumerable___closed__2_value) as *mut LeanObject;
pub static mut l_UInt8_instUpwardEnumerable: *mut LeanObject =
    core::ptr::addr_of!(l_UInt8_instUpwardEnumerable___closed__2_value) as *mut LeanObject;
pub static l_UInt8_instLeast_x3f___closed__0_value: LeanCtorObject<1> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 1,
    },
    m_objs: [(((0 as usize) << 1) | 1) as *mut LeanObject],
};
static mut l_UInt8_instLeast_x3f___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_UInt8_instLeast_x3f___closed__0_value) as *mut LeanObject;
pub static mut l_UInt8_instLeast_x3f: *mut LeanObject =
    core::ptr::addr_of!(l_UInt8_instLeast_x3f___closed__0_value) as *mut LeanObject;
pub static l_UInt8_instHasSize___closed__0_value: LeanClosureObject<0> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_UInt8_instHasSize___lam__0___boxed as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_UInt8_instHasSize___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_UInt8_instHasSize___closed__0_value) as *mut LeanObject;
pub static mut l_UInt8_instHasSize: *mut LeanObject =
    core::ptr::addr_of!(l_UInt8_instHasSize___closed__0_value) as *mut LeanObject;
pub static l_UInt8_instHasSize__1___closed__0_value: LeanClosureObject<0> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_UInt8_instHasSize__1___lam__0___boxed as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_UInt8_instHasSize__1___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_UInt8_instHasSize__1___closed__0_value) as *mut LeanObject;
pub static mut l_UInt8_instHasSize__1: *mut LeanObject =
    core::ptr::addr_of!(l_UInt8_instHasSize__1___closed__0_value) as *mut LeanObject;
pub static l_UInt8_instHasSize__2___closed__0_value: LeanClosureObject<0> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_UInt8_instHasSize__2___lam__0___boxed as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_UInt8_instHasSize__2___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_UInt8_instHasSize__2___closed__0_value) as *mut LeanObject;
pub static mut l_UInt8_instHasSize__2: *mut LeanObject =
    core::ptr::addr_of!(l_UInt8_instHasSize__2___closed__0_value) as *mut LeanObject;
pub static l_UInt16_instUpwardEnumerable___closed__0_value: LeanClosureObject<0> =
    LeanClosureObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_UInt16_instUpwardEnumerable___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_UInt16_instUpwardEnumerable___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_UInt16_instUpwardEnumerable___closed__0_value) as *mut LeanObject;
pub static l_UInt16_instUpwardEnumerable___closed__1_value: LeanClosureObject<0> =
    LeanClosureObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_UInt16_instUpwardEnumerable___lam__1___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_UInt16_instUpwardEnumerable___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_UInt16_instUpwardEnumerable___closed__1_value) as *mut LeanObject;
pub static l_UInt16_instUpwardEnumerable___closed__2_value: LeanCtorObject<2> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 0,
    },
    m_objs: [
        core::ptr::addr_of!(l_UInt16_instUpwardEnumerable___closed__0_value) as *mut LeanObject,
        core::ptr::addr_of!(l_UInt16_instUpwardEnumerable___closed__1_value) as *mut LeanObject,
    ],
};
static mut l_UInt16_instUpwardEnumerable___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_UInt16_instUpwardEnumerable___closed__2_value) as *mut LeanObject;
pub static mut l_UInt16_instUpwardEnumerable: *mut LeanObject =
    core::ptr::addr_of!(l_UInt16_instUpwardEnumerable___closed__2_value) as *mut LeanObject;
pub static l_UInt16_instLeast_x3f___closed__0_value: LeanCtorObject<1> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 1,
    },
    m_objs: [(((0 as usize) << 1) | 1) as *mut LeanObject],
};
static mut l_UInt16_instLeast_x3f___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_UInt16_instLeast_x3f___closed__0_value) as *mut LeanObject;
pub static mut l_UInt16_instLeast_x3f: *mut LeanObject =
    core::ptr::addr_of!(l_UInt16_instLeast_x3f___closed__0_value) as *mut LeanObject;
pub static l_UInt16_instHasSize___closed__0_value: LeanClosureObject<0> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_UInt16_instHasSize___lam__0___boxed as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_UInt16_instHasSize___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_UInt16_instHasSize___closed__0_value) as *mut LeanObject;
pub static mut l_UInt16_instHasSize: *mut LeanObject =
    core::ptr::addr_of!(l_UInt16_instHasSize___closed__0_value) as *mut LeanObject;
pub static l_UInt16_instHasSize__1___closed__0_value: LeanClosureObject<0> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_UInt16_instHasSize__1___lam__0___boxed as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_UInt16_instHasSize__1___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_UInt16_instHasSize__1___closed__0_value) as *mut LeanObject;
pub static mut l_UInt16_instHasSize__1: *mut LeanObject =
    core::ptr::addr_of!(l_UInt16_instHasSize__1___closed__0_value) as *mut LeanObject;
pub static l_UInt16_instHasSize__2___closed__0_value: LeanClosureObject<0> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_UInt16_instHasSize__2___lam__0___boxed as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_UInt16_instHasSize__2___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_UInt16_instHasSize__2___closed__0_value) as *mut LeanObject;
pub static mut l_UInt16_instHasSize__2: *mut LeanObject =
    core::ptr::addr_of!(l_UInt16_instHasSize__2___closed__0_value) as *mut LeanObject;
pub static l_UInt32_instUpwardEnumerable___closed__0_value: LeanClosureObject<0> =
    LeanClosureObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_UInt32_instUpwardEnumerable___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_UInt32_instUpwardEnumerable___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_UInt32_instUpwardEnumerable___closed__0_value) as *mut LeanObject;
pub static l_UInt32_instUpwardEnumerable___closed__1_value: LeanClosureObject<0> =
    LeanClosureObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_UInt32_instUpwardEnumerable___lam__1___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_UInt32_instUpwardEnumerable___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_UInt32_instUpwardEnumerable___closed__1_value) as *mut LeanObject;
pub static l_UInt32_instUpwardEnumerable___closed__2_value: LeanCtorObject<2> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 0,
    },
    m_objs: [
        core::ptr::addr_of!(l_UInt32_instUpwardEnumerable___closed__0_value) as *mut LeanObject,
        core::ptr::addr_of!(l_UInt32_instUpwardEnumerable___closed__1_value) as *mut LeanObject,
    ],
};
static mut l_UInt32_instUpwardEnumerable___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_UInt32_instUpwardEnumerable___closed__2_value) as *mut LeanObject;
pub static mut l_UInt32_instUpwardEnumerable: *mut LeanObject =
    core::ptr::addr_of!(l_UInt32_instUpwardEnumerable___closed__2_value) as *mut LeanObject;
pub static mut l_UInt32_instLeast_x3f___closed__0___boxed__const__1: *mut LeanObject =
    core::ptr::null_mut();
static mut l_UInt32_instLeast_x3f___closed__0_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_UInt32_instLeast_x3f___closed__0: *mut LeanObject = core::ptr::null_mut();
pub static mut l_UInt32_instLeast_x3f: *mut LeanObject = core::ptr::null_mut();
pub static l_UInt32_instHasSize___closed__0_value: LeanClosureObject<0> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_UInt32_instHasSize___lam__0___boxed as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_UInt32_instHasSize___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_UInt32_instHasSize___closed__0_value) as *mut LeanObject;
pub static mut l_UInt32_instHasSize: *mut LeanObject =
    core::ptr::addr_of!(l_UInt32_instHasSize___closed__0_value) as *mut LeanObject;
pub static l_UInt32_instHasSize__1___closed__0_value: LeanClosureObject<0> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_UInt32_instHasSize__1___lam__0___boxed as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_UInt32_instHasSize__1___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_UInt32_instHasSize__1___closed__0_value) as *mut LeanObject;
pub static mut l_UInt32_instHasSize__1: *mut LeanObject =
    core::ptr::addr_of!(l_UInt32_instHasSize__1___closed__0_value) as *mut LeanObject;
pub static l_UInt32_instHasSize__2___closed__0_value: LeanClosureObject<0> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_UInt32_instHasSize__2___lam__0___boxed as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_UInt32_instHasSize__2___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_UInt32_instHasSize__2___closed__0_value) as *mut LeanObject;
pub static mut l_UInt32_instHasSize__2: *mut LeanObject =
    core::ptr::addr_of!(l_UInt32_instHasSize__2___closed__0_value) as *mut LeanObject;
static mut l_UInt64_instUpwardEnumerable___lam__1___closed__0_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_UInt64_instUpwardEnumerable___lam__1___closed__0: *mut LeanObject =
    core::ptr::null_mut();
pub static l_UInt64_instUpwardEnumerable___closed__0_value: LeanClosureObject<0> =
    LeanClosureObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_UInt64_instUpwardEnumerable___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_UInt64_instUpwardEnumerable___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_UInt64_instUpwardEnumerable___closed__0_value) as *mut LeanObject;
pub static l_UInt64_instUpwardEnumerable___closed__1_value: LeanClosureObject<0> =
    LeanClosureObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_UInt64_instUpwardEnumerable___lam__1___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_UInt64_instUpwardEnumerable___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_UInt64_instUpwardEnumerable___closed__1_value) as *mut LeanObject;
pub static l_UInt64_instUpwardEnumerable___closed__2_value: LeanCtorObject<2> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 0,
    },
    m_objs: [
        core::ptr::addr_of!(l_UInt64_instUpwardEnumerable___closed__0_value) as *mut LeanObject,
        core::ptr::addr_of!(l_UInt64_instUpwardEnumerable___closed__1_value) as *mut LeanObject,
    ],
};
static mut l_UInt64_instUpwardEnumerable___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_UInt64_instUpwardEnumerable___closed__2_value) as *mut LeanObject;
pub static mut l_UInt64_instUpwardEnumerable: *mut LeanObject =
    core::ptr::addr_of!(l_UInt64_instUpwardEnumerable___closed__2_value) as *mut LeanObject;
pub static l_UInt64_instLeast_x3f___closed__0___boxed__const__1_value: LeanCtorObject<1> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 0
                + 8) as u16,
            other: 0,
            tag: 0,
        },
        m_objs: [0 as *mut LeanObject],
    };
pub static mut l_UInt64_instLeast_x3f___closed__0___boxed__const__1: *mut LeanObject =
    core::ptr::addr_of!(l_UInt64_instLeast_x3f___closed__0___boxed__const__1_value)
        as *mut LeanObject;
pub static l_UInt64_instLeast_x3f___closed__0_value: LeanCtorObject<1> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_UInt64_instLeast_x3f___closed__0___boxed__const__1_value)
            as *mut LeanObject,
    ],
};
static mut l_UInt64_instLeast_x3f___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_UInt64_instLeast_x3f___closed__0_value) as *mut LeanObject;
pub static mut l_UInt64_instLeast_x3f: *mut LeanObject =
    core::ptr::addr_of!(l_UInt64_instLeast_x3f___closed__0_value) as *mut LeanObject;
pub static l_UInt64_instHasSize___closed__0_value: LeanClosureObject<0> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_UInt64_instHasSize___lam__0___boxed as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_UInt64_instHasSize___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_UInt64_instHasSize___closed__0_value) as *mut LeanObject;
pub static mut l_UInt64_instHasSize: *mut LeanObject =
    core::ptr::addr_of!(l_UInt64_instHasSize___closed__0_value) as *mut LeanObject;
pub static l_UInt64_instHasSize__1___closed__0_value: LeanClosureObject<0> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_UInt64_instHasSize__1___lam__0___boxed as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_UInt64_instHasSize__1___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_UInt64_instHasSize__1___closed__0_value) as *mut LeanObject;
pub static mut l_UInt64_instHasSize__1: *mut LeanObject =
    core::ptr::addr_of!(l_UInt64_instHasSize__1___closed__0_value) as *mut LeanObject;
pub static l_UInt64_instHasSize__2___closed__0_value: LeanClosureObject<0> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_UInt64_instHasSize__2___lam__0___boxed as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_UInt64_instHasSize__2___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_UInt64_instHasSize__2___closed__0_value) as *mut LeanObject;
pub static mut l_UInt64_instHasSize__2: *mut LeanObject =
    core::ptr::addr_of!(l_UInt64_instHasSize__2___closed__0_value) as *mut LeanObject;
static mut l_USize_instUpwardEnumerable___lam__1___closed__0_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_USize_instUpwardEnumerable___lam__1___closed__0: *mut LeanObject =
    core::ptr::null_mut();
pub static l_USize_instUpwardEnumerable___closed__0_value: LeanClosureObject<0> =
    LeanClosureObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_USize_instUpwardEnumerable___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_USize_instUpwardEnumerable___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_USize_instUpwardEnumerable___closed__0_value) as *mut LeanObject;
pub static l_USize_instUpwardEnumerable___closed__1_value: LeanClosureObject<0> =
    LeanClosureObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_USize_instUpwardEnumerable___lam__1___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_USize_instUpwardEnumerable___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_USize_instUpwardEnumerable___closed__1_value) as *mut LeanObject;
pub static l_USize_instUpwardEnumerable___closed__2_value: LeanCtorObject<2> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 0,
    },
    m_objs: [
        core::ptr::addr_of!(l_USize_instUpwardEnumerable___closed__0_value) as *mut LeanObject,
        core::ptr::addr_of!(l_USize_instUpwardEnumerable___closed__1_value) as *mut LeanObject,
    ],
};
static mut l_USize_instUpwardEnumerable___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_USize_instUpwardEnumerable___closed__2_value) as *mut LeanObject;
pub static mut l_USize_instUpwardEnumerable: *mut LeanObject =
    core::ptr::addr_of!(l_USize_instUpwardEnumerable___closed__2_value) as *mut LeanObject;
pub static l_USize_instLeast_x3f___closed__0___boxed__const__1_value: LeanCtorObject<1> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 1
                + core::mem::size_of::<usize>() * 1) as u16,
            other: 1,
            tag: 0,
        },
        m_objs: [(0 as *mut LeanObject)],
    };
pub static mut l_USize_instLeast_x3f___closed__0___boxed__const__1: *mut LeanObject =
    core::ptr::addr_of!(l_USize_instLeast_x3f___closed__0___boxed__const__1_value)
        as *mut LeanObject;
pub static l_USize_instLeast_x3f___closed__0_value: LeanCtorObject<1> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_USize_instLeast_x3f___closed__0___boxed__const__1_value)
            as *mut LeanObject,
    ],
};
static mut l_USize_instLeast_x3f___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_USize_instLeast_x3f___closed__0_value) as *mut LeanObject;
pub static mut l_USize_instLeast_x3f: *mut LeanObject =
    core::ptr::addr_of!(l_USize_instLeast_x3f___closed__0_value) as *mut LeanObject;
pub static l_USize_instHasSize___closed__0_value: LeanClosureObject<0> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_USize_instHasSize___lam__0___boxed as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_USize_instHasSize___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_USize_instHasSize___closed__0_value) as *mut LeanObject;
pub static mut l_USize_instHasSize: *mut LeanObject =
    core::ptr::addr_of!(l_USize_instHasSize___closed__0_value) as *mut LeanObject;
pub static l_USize_instHasSize__1___closed__0_value: LeanClosureObject<0> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_USize_instHasSize__1___lam__0___boxed as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_USize_instHasSize__1___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_USize_instHasSize__1___closed__0_value) as *mut LeanObject;
pub static mut l_USize_instHasSize__1: *mut LeanObject =
    core::ptr::addr_of!(l_USize_instHasSize__1___closed__0_value) as *mut LeanObject;
pub static l_USize_instHasSize__2___closed__0_value: LeanClosureObject<0> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_USize_instHasSize__2___lam__0___boxed as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_USize_instHasSize__2___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_USize_instHasSize__2___closed__0_value) as *mut LeanObject;
pub static mut l_USize_instHasSize__2: *mut LeanObject =
    core::ptr::addr_of!(l_USize_instHasSize__2___closed__0_value) as *mut LeanObject;
pub unsafe fn l_UInt8_instUpwardEnumerable___lam__0(mut v_i_373_: u8) -> *mut LeanObject {
    let mut v___x_374_: u8 = 0;
    let mut v___x_375_: u8 = 0;
    let mut v___x_376_: u8 = 0;
    let mut v___x_377_: u8 = 0;
    v___x_374_ = 1;
    v___x_375_ = lean_uint8_add(v_i_373_, v___x_374_);
    v___x_376_ = 0;
    v___x_377_ = lean_uint8_dec_eq(v___x_375_, v___x_376_);
    if v___x_377_ == 0 {
        let mut v___x_378_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_379_: *mut LeanObject = core::ptr::null_mut();
        v___x_378_ = lean_box((v___x_375_) as usize);
        v___x_379_ = lean_alloc_ctor(1, 1, (0) as u32);
        lean_ctor_set(v___x_379_, 0, v___x_378_);
        return v___x_379_;
    } else {
        let mut v___x_380_: *mut LeanObject = core::ptr::null_mut();
        v___x_380_ = lean_box(0);
        return v___x_380_;
    }
}
pub unsafe fn l_UInt8_instUpwardEnumerable___lam__0___boxed(
    mut v_i_381_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_i_boxed_382_: u8 = 0;
    let mut v_res_383_: *mut LeanObject = core::ptr::null_mut();
    v_i_boxed_382_ = (lean_unbox(v_i_381_) as u8);
    v_res_383_ = l_UInt8_instUpwardEnumerable___lam__0(v_i_boxed_382_);
    return v_res_383_;
}
pub unsafe fn l_UInt8_instUpwardEnumerable___lam__1(
    mut v_n_384_: *mut LeanObject,
    mut v_i_385_: u8,
) -> *mut LeanObject {
    let mut v___x_386_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_387_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_388_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_389_: u8 = 0;
    v___x_386_ = lean_uint8_to_nat(v_i_385_);
    v___x_387_ = lean_nat_add(v___x_386_, v_n_384_);
    v___x_388_ = lean_unsigned_to_nat(256);
    v___x_389_ = lean_nat_dec_lt(v___x_387_, v___x_388_);
    if v___x_389_ == 0 {
        let mut v___x_390_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v___x_387_);
        v___x_390_ = lean_box(0);
        return v___x_390_;
    } else {
        let mut v___x_391_: u8 = 0;
        let mut v___x_392_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_393_: *mut LeanObject = core::ptr::null_mut();
        v___x_391_ = lean_uint8_of_nat(v___x_387_);
        lean_dec(v___x_387_);
        v___x_392_ = lean_box((v___x_391_) as usize);
        v___x_393_ = lean_alloc_ctor(1, 1, (0) as u32);
        lean_ctor_set(v___x_393_, 0, v___x_392_);
        return v___x_393_;
    }
}
pub unsafe fn l_UInt8_instUpwardEnumerable___lam__1___boxed(
    mut v_n_394_: *mut LeanObject,
    mut v_i_395_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_i_boxed_396_: u8 = 0;
    let mut v_res_397_: *mut LeanObject = core::ptr::null_mut();
    v_i_boxed_396_ = (lean_unbox(v_i_395_) as u8);
    v_res_397_ = l_UInt8_instUpwardEnumerable___lam__1(v_n_394_, v_i_boxed_396_);
    lean_dec(v_n_394_);
    return v_res_397_;
}
pub unsafe fn l_UInt8_instHasSize___lam__0(
    mut v_lo_408_: u8,
    mut v_hi_409_: u8,
) -> *mut LeanObject {
    let mut v___x_410_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_411_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_412_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_413_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_414_: *mut LeanObject = core::ptr::null_mut();
    v___x_410_ = lean_uint8_to_nat(v_hi_409_);
    v___x_411_ = lean_unsigned_to_nat(1);
    v___x_412_ = lean_nat_add(v___x_410_, v___x_411_);
    v___x_413_ = lean_uint8_to_nat(v_lo_408_);
    v___x_414_ = lean_nat_sub(v___x_412_, v___x_413_);
    lean_dec(v___x_412_);
    return v___x_414_;
}
pub unsafe fn l_UInt8_instHasSize___lam__0___boxed(
    mut v_lo_415_: *mut LeanObject,
    mut v_hi_416_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_lo_boxed_417_: u8 = 0;
    let mut v_hi_boxed_418_: u8 = 0;
    let mut v_res_419_: *mut LeanObject = core::ptr::null_mut();
    v_lo_boxed_417_ = (lean_unbox(v_lo_415_) as u8);
    v_hi_boxed_418_ = (lean_unbox(v_hi_416_) as u8);
    v_res_419_ = l_UInt8_instHasSize___lam__0(v_lo_boxed_417_, v_hi_boxed_418_);
    return v_res_419_;
}
pub unsafe fn l_UInt8_instHasSize__1___lam__0(
    mut v_lo_422_: u8,
    mut v_hi_423_: u8,
) -> *mut LeanObject {
    let mut v___x_424_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_425_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_426_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_427_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_428_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_429_: *mut LeanObject = core::ptr::null_mut();
    v___x_424_ = lean_uint8_to_nat(v_hi_423_);
    v___x_425_ = lean_unsigned_to_nat(1);
    v___x_426_ = lean_nat_add(v___x_424_, v___x_425_);
    v___x_427_ = lean_uint8_to_nat(v_lo_422_);
    v___x_428_ = lean_nat_sub(v___x_426_, v___x_427_);
    lean_dec(v___x_426_);
    v___x_429_ = lean_nat_sub(v___x_428_, v___x_425_);
    lean_dec(v___x_428_);
    return v___x_429_;
}
pub unsafe fn l_UInt8_instHasSize__1___lam__0___boxed(
    mut v_lo_430_: *mut LeanObject,
    mut v_hi_431_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_lo_boxed_432_: u8 = 0;
    let mut v_hi_boxed_433_: u8 = 0;
    let mut v_res_434_: *mut LeanObject = core::ptr::null_mut();
    v_lo_boxed_432_ = (lean_unbox(v_lo_430_) as u8);
    v_hi_boxed_433_ = (lean_unbox(v_hi_431_) as u8);
    v_res_434_ = l_UInt8_instHasSize__1___lam__0(v_lo_boxed_432_, v_hi_boxed_433_);
    return v_res_434_;
}
pub unsafe fn l_UInt8_instHasSize__2___lam__0(mut v_lo_437_: u8) -> *mut LeanObject {
    let mut v___x_438_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_439_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_440_: *mut LeanObject = core::ptr::null_mut();
    v___x_438_ = lean_unsigned_to_nat(256);
    v___x_439_ = lean_uint8_to_nat(v_lo_437_);
    v___x_440_ = lean_nat_sub(v___x_438_, v___x_439_);
    return v___x_440_;
}
pub unsafe fn l_UInt8_instHasSize__2___lam__0___boxed(
    mut v_lo_441_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_lo_boxed_442_: u8 = 0;
    let mut v_res_443_: *mut LeanObject = core::ptr::null_mut();
    v_lo_boxed_442_ = (lean_unbox(v_lo_441_) as u8);
    v_res_443_ = l_UInt8_instHasSize__2___lam__0(v_lo_boxed_442_);
    return v_res_443_;
}
pub unsafe fn l_UInt16_instUpwardEnumerable___lam__0(mut v_i_446_: u16) -> *mut LeanObject {
    let mut v___x_447_: u16 = 0;
    let mut v___x_448_: u16 = 0;
    let mut v___x_449_: u16 = 0;
    let mut v___x_450_: u8 = 0;
    v___x_447_ = 1;
    v___x_448_ = lean_uint16_add(v_i_446_, v___x_447_);
    v___x_449_ = 0;
    v___x_450_ = lean_uint16_dec_eq(v___x_448_, v___x_449_);
    if v___x_450_ == 0 {
        let mut v___x_451_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_452_: *mut LeanObject = core::ptr::null_mut();
        v___x_451_ = lean_box((v___x_448_) as usize);
        v___x_452_ = lean_alloc_ctor(1, 1, (0) as u32);
        lean_ctor_set(v___x_452_, 0, v___x_451_);
        return v___x_452_;
    } else {
        let mut v___x_453_: *mut LeanObject = core::ptr::null_mut();
        v___x_453_ = lean_box(0);
        return v___x_453_;
    }
}
pub unsafe fn l_UInt16_instUpwardEnumerable___lam__0___boxed(
    mut v_i_454_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_i_boxed_455_: u16 = 0;
    let mut v_res_456_: *mut LeanObject = core::ptr::null_mut();
    v_i_boxed_455_ = (lean_unbox(v_i_454_) as u16);
    v_res_456_ = l_UInt16_instUpwardEnumerable___lam__0(v_i_boxed_455_);
    return v_res_456_;
}
pub unsafe fn l_UInt16_instUpwardEnumerable___lam__1(
    mut v_n_457_: *mut LeanObject,
    mut v_i_458_: u16,
) -> *mut LeanObject {
    let mut v___x_459_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_460_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_461_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_462_: u8 = 0;
    v___x_459_ = lean_uint16_to_nat(v_i_458_);
    v___x_460_ = lean_nat_add(v___x_459_, v_n_457_);
    v___x_461_ = lean_unsigned_to_nat(65536);
    v___x_462_ = lean_nat_dec_lt(v___x_460_, v___x_461_);
    if v___x_462_ == 0 {
        let mut v___x_463_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v___x_460_);
        v___x_463_ = lean_box(0);
        return v___x_463_;
    } else {
        let mut v___x_464_: u16 = 0;
        let mut v___x_465_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_466_: *mut LeanObject = core::ptr::null_mut();
        v___x_464_ = lean_uint16_of_nat(v___x_460_);
        lean_dec(v___x_460_);
        v___x_465_ = lean_box((v___x_464_) as usize);
        v___x_466_ = lean_alloc_ctor(1, 1, (0) as u32);
        lean_ctor_set(v___x_466_, 0, v___x_465_);
        return v___x_466_;
    }
}
pub unsafe fn l_UInt16_instUpwardEnumerable___lam__1___boxed(
    mut v_n_467_: *mut LeanObject,
    mut v_i_468_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_i_boxed_469_: u16 = 0;
    let mut v_res_470_: *mut LeanObject = core::ptr::null_mut();
    v_i_boxed_469_ = (lean_unbox(v_i_468_) as u16);
    v_res_470_ = l_UInt16_instUpwardEnumerable___lam__1(v_n_467_, v_i_boxed_469_);
    lean_dec(v_n_467_);
    return v_res_470_;
}
pub unsafe fn l_UInt16_instHasSize___lam__0(
    mut v_lo_481_: u16,
    mut v_hi_482_: u16,
) -> *mut LeanObject {
    let mut v___x_483_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_484_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_485_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_486_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_487_: *mut LeanObject = core::ptr::null_mut();
    v___x_483_ = lean_uint16_to_nat(v_hi_482_);
    v___x_484_ = lean_unsigned_to_nat(1);
    v___x_485_ = lean_nat_add(v___x_483_, v___x_484_);
    v___x_486_ = lean_uint16_to_nat(v_lo_481_);
    v___x_487_ = lean_nat_sub(v___x_485_, v___x_486_);
    lean_dec(v___x_485_);
    return v___x_487_;
}
pub unsafe fn l_UInt16_instHasSize___lam__0___boxed(
    mut v_lo_488_: *mut LeanObject,
    mut v_hi_489_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_lo_boxed_490_: u16 = 0;
    let mut v_hi_boxed_491_: u16 = 0;
    let mut v_res_492_: *mut LeanObject = core::ptr::null_mut();
    v_lo_boxed_490_ = (lean_unbox(v_lo_488_) as u16);
    v_hi_boxed_491_ = (lean_unbox(v_hi_489_) as u16);
    v_res_492_ = l_UInt16_instHasSize___lam__0(v_lo_boxed_490_, v_hi_boxed_491_);
    return v_res_492_;
}
pub unsafe fn l_UInt16_instHasSize__1___lam__0(
    mut v_lo_495_: u16,
    mut v_hi_496_: u16,
) -> *mut LeanObject {
    let mut v___x_497_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_498_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_499_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_500_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_501_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_502_: *mut LeanObject = core::ptr::null_mut();
    v___x_497_ = lean_uint16_to_nat(v_hi_496_);
    v___x_498_ = lean_unsigned_to_nat(1);
    v___x_499_ = lean_nat_add(v___x_497_, v___x_498_);
    v___x_500_ = lean_uint16_to_nat(v_lo_495_);
    v___x_501_ = lean_nat_sub(v___x_499_, v___x_500_);
    lean_dec(v___x_499_);
    v___x_502_ = lean_nat_sub(v___x_501_, v___x_498_);
    lean_dec(v___x_501_);
    return v___x_502_;
}
pub unsafe fn l_UInt16_instHasSize__1___lam__0___boxed(
    mut v_lo_503_: *mut LeanObject,
    mut v_hi_504_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_lo_boxed_505_: u16 = 0;
    let mut v_hi_boxed_506_: u16 = 0;
    let mut v_res_507_: *mut LeanObject = core::ptr::null_mut();
    v_lo_boxed_505_ = (lean_unbox(v_lo_503_) as u16);
    v_hi_boxed_506_ = (lean_unbox(v_hi_504_) as u16);
    v_res_507_ = l_UInt16_instHasSize__1___lam__0(v_lo_boxed_505_, v_hi_boxed_506_);
    return v_res_507_;
}
pub unsafe fn l_UInt16_instHasSize__2___lam__0(mut v_lo_510_: u16) -> *mut LeanObject {
    let mut v___x_511_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_512_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_513_: *mut LeanObject = core::ptr::null_mut();
    v___x_511_ = lean_unsigned_to_nat(65536);
    v___x_512_ = lean_uint16_to_nat(v_lo_510_);
    v___x_513_ = lean_nat_sub(v___x_511_, v___x_512_);
    return v___x_513_;
}
pub unsafe fn l_UInt16_instHasSize__2___lam__0___boxed(
    mut v_lo_514_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_lo_boxed_515_: u16 = 0;
    let mut v_res_516_: *mut LeanObject = core::ptr::null_mut();
    v_lo_boxed_515_ = (lean_unbox(v_lo_514_) as u16);
    v_res_516_ = l_UInt16_instHasSize__2___lam__0(v_lo_boxed_515_);
    return v_res_516_;
}
pub unsafe fn l_UInt32_instUpwardEnumerable___lam__0(mut v_i_519_: u32) -> *mut LeanObject {
    let mut v___x_520_: u32 = 0;
    let mut v___x_521_: u32 = 0;
    let mut v___x_522_: u32 = 0;
    let mut v___x_523_: u8 = 0;
    v___x_520_ = 1;
    v___x_521_ = lean_uint32_add(v_i_519_, v___x_520_);
    v___x_522_ = 0;
    v___x_523_ = lean_uint32_dec_eq(v___x_521_, v___x_522_);
    if v___x_523_ == 0 {
        let mut v___x_524_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_525_: *mut LeanObject = core::ptr::null_mut();
        v___x_524_ = lean_box_uint32(v___x_521_);
        v___x_525_ = lean_alloc_ctor(1, 1, (0) as u32);
        lean_ctor_set(v___x_525_, 0, v___x_524_);
        return v___x_525_;
    } else {
        let mut v___x_526_: *mut LeanObject = core::ptr::null_mut();
        v___x_526_ = lean_box(0);
        return v___x_526_;
    }
}
pub unsafe fn l_UInt32_instUpwardEnumerable___lam__0___boxed(
    mut v_i_527_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_i_boxed_528_: u32 = 0;
    let mut v_res_529_: *mut LeanObject = core::ptr::null_mut();
    v_i_boxed_528_ = lean_unbox_uint32(v_i_527_);
    lean_dec(v_i_527_);
    v_res_529_ = l_UInt32_instUpwardEnumerable___lam__0(v_i_boxed_528_);
    return v_res_529_;
}
pub unsafe fn l_UInt32_instUpwardEnumerable___lam__1(
    mut v_n_530_: *mut LeanObject,
    mut v_i_531_: u32,
) -> *mut LeanObject {
    let mut v___x_532_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_533_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_534_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_535_: u8 = 0;
    v___x_532_ = lean_uint32_to_nat(v_i_531_);
    v___x_533_ = lean_nat_add(v___x_532_, v_n_530_);
    lean_dec(v___x_532_);
    v___x_534_ = lean_cstr_to_nat(b"4294967296\0".as_ptr().cast());
    v___x_535_ = lean_nat_dec_lt(v___x_533_, v___x_534_);
    if v___x_535_ == 0 {
        let mut v___x_536_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v___x_533_);
        v___x_536_ = lean_box(0);
        return v___x_536_;
    } else {
        let mut v___x_537_: u32 = 0;
        let mut v___x_538_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_539_: *mut LeanObject = core::ptr::null_mut();
        v___x_537_ = lean_uint32_of_nat(v___x_533_);
        lean_dec(v___x_533_);
        v___x_538_ = lean_box_uint32(v___x_537_);
        v___x_539_ = lean_alloc_ctor(1, 1, (0) as u32);
        lean_ctor_set(v___x_539_, 0, v___x_538_);
        return v___x_539_;
    }
}
pub unsafe fn l_UInt32_instUpwardEnumerable___lam__1___boxed(
    mut v_n_540_: *mut LeanObject,
    mut v_i_541_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_i_boxed_542_: u32 = 0;
    let mut v_res_543_: *mut LeanObject = core::ptr::null_mut();
    v_i_boxed_542_ = lean_unbox_uint32(v_i_541_);
    lean_dec(v_i_541_);
    v_res_543_ = l_UInt32_instUpwardEnumerable___lam__1(v_n_540_, v_i_boxed_542_);
    lean_dec(v_n_540_);
    return v_res_543_;
}
pub unsafe fn _init_l_UInt32_instLeast_x3f___closed__0___boxed__const__1() -> *mut LeanObject {
    let mut v___x_550_: u32 = 0;
    let mut v___x_551_: *mut LeanObject = core::ptr::null_mut();
    v___x_550_ = 0;
    v___x_551_ = lean_box_uint32(v___x_550_);
    return v___x_551_;
}
pub unsafe fn _init_l_UInt32_instLeast_x3f___closed__0() -> *mut LeanObject {
    let mut v___x_552_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_553_: *mut LeanObject = core::ptr::null_mut();
    v___x_552_ = l_UInt32_instLeast_x3f___closed__0___boxed__const__1;
    v___x_553_ = lean_alloc_ctor(1, 1, (0) as u32);
    lean_ctor_set(v___x_553_, 0, v___x_552_);
    return v___x_553_;
}
pub unsafe fn _init_l_UInt32_instLeast_x3f() -> *mut LeanObject {
    let mut v___x_554_: *mut LeanObject = core::ptr::null_mut();
    v___x_554_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_UInt32_instLeast_x3f___closed__0),
        core::ptr::addr_of_mut!(l_UInt32_instLeast_x3f___closed__0_once),
        _init_l_UInt32_instLeast_x3f___closed__0,
    );
    return v___x_554_;
}
pub unsafe fn l_UInt32_instHasSize___lam__0(
    mut v_lo_555_: u32,
    mut v_hi_556_: u32,
) -> *mut LeanObject {
    let mut v___x_557_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_558_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_559_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_560_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_561_: *mut LeanObject = core::ptr::null_mut();
    v___x_557_ = lean_uint32_to_nat(v_hi_556_);
    v___x_558_ = lean_unsigned_to_nat(1);
    v___x_559_ = lean_nat_add(v___x_557_, v___x_558_);
    lean_dec(v___x_557_);
    v___x_560_ = lean_uint32_to_nat(v_lo_555_);
    v___x_561_ = lean_nat_sub(v___x_559_, v___x_560_);
    lean_dec(v___x_560_);
    lean_dec(v___x_559_);
    return v___x_561_;
}
pub unsafe fn l_UInt32_instHasSize___lam__0___boxed(
    mut v_lo_562_: *mut LeanObject,
    mut v_hi_563_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_lo_boxed_564_: u32 = 0;
    let mut v_hi_boxed_565_: u32 = 0;
    let mut v_res_566_: *mut LeanObject = core::ptr::null_mut();
    v_lo_boxed_564_ = lean_unbox_uint32(v_lo_562_);
    lean_dec(v_lo_562_);
    v_hi_boxed_565_ = lean_unbox_uint32(v_hi_563_);
    lean_dec(v_hi_563_);
    v_res_566_ = l_UInt32_instHasSize___lam__0(v_lo_boxed_564_, v_hi_boxed_565_);
    return v_res_566_;
}
pub unsafe fn l_UInt32_instHasSize__1___lam__0(
    mut v_lo_569_: u32,
    mut v_hi_570_: u32,
) -> *mut LeanObject {
    let mut v___x_571_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_572_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_573_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_574_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_575_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_576_: *mut LeanObject = core::ptr::null_mut();
    v___x_571_ = lean_uint32_to_nat(v_hi_570_);
    v___x_572_ = lean_unsigned_to_nat(1);
    v___x_573_ = lean_nat_add(v___x_571_, v___x_572_);
    lean_dec(v___x_571_);
    v___x_574_ = lean_uint32_to_nat(v_lo_569_);
    v___x_575_ = lean_nat_sub(v___x_573_, v___x_574_);
    lean_dec(v___x_574_);
    lean_dec(v___x_573_);
    v___x_576_ = lean_nat_sub(v___x_575_, v___x_572_);
    lean_dec(v___x_575_);
    return v___x_576_;
}
pub unsafe fn l_UInt32_instHasSize__1___lam__0___boxed(
    mut v_lo_577_: *mut LeanObject,
    mut v_hi_578_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_lo_boxed_579_: u32 = 0;
    let mut v_hi_boxed_580_: u32 = 0;
    let mut v_res_581_: *mut LeanObject = core::ptr::null_mut();
    v_lo_boxed_579_ = lean_unbox_uint32(v_lo_577_);
    lean_dec(v_lo_577_);
    v_hi_boxed_580_ = lean_unbox_uint32(v_hi_578_);
    lean_dec(v_hi_578_);
    v_res_581_ = l_UInt32_instHasSize__1___lam__0(v_lo_boxed_579_, v_hi_boxed_580_);
    return v_res_581_;
}
pub unsafe fn l_UInt32_instHasSize__2___lam__0(mut v_lo_584_: u32) -> *mut LeanObject {
    let mut v___x_585_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_586_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_587_: *mut LeanObject = core::ptr::null_mut();
    v___x_585_ = lean_cstr_to_nat(b"4294967296\0".as_ptr().cast());
    v___x_586_ = lean_uint32_to_nat(v_lo_584_);
    v___x_587_ = lean_nat_sub(v___x_585_, v___x_586_);
    lean_dec(v___x_586_);
    return v___x_587_;
}
pub unsafe fn l_UInt32_instHasSize__2___lam__0___boxed(
    mut v_lo_588_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_lo_boxed_589_: u32 = 0;
    let mut v_res_590_: *mut LeanObject = core::ptr::null_mut();
    v_lo_boxed_589_ = lean_unbox_uint32(v_lo_588_);
    lean_dec(v_lo_588_);
    v_res_590_ = l_UInt32_instHasSize__2___lam__0(v_lo_boxed_589_);
    return v_res_590_;
}
pub unsafe fn l_UInt64_instUpwardEnumerable___lam__0(mut v_i_593_: u64) -> *mut LeanObject {
    let mut v___x_594_: u64 = 0;
    let mut v___x_595_: u64 = 0;
    let mut v___x_596_: u64 = 0;
    let mut v___x_597_: u8 = 0;
    v___x_594_ = 1u64;
    v___x_595_ = lean_uint64_add(v_i_593_, v___x_594_);
    v___x_596_ = 0u64;
    v___x_597_ = lean_uint64_dec_eq(v___x_595_, v___x_596_);
    if v___x_597_ == 0 {
        let mut v___x_598_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_599_: *mut LeanObject = core::ptr::null_mut();
        v___x_598_ = lean_box_uint64(v___x_595_);
        v___x_599_ = lean_alloc_ctor(1, 1, (0) as u32);
        lean_ctor_set(v___x_599_, 0, v___x_598_);
        return v___x_599_;
    } else {
        let mut v___x_600_: *mut LeanObject = core::ptr::null_mut();
        v___x_600_ = lean_box(0);
        return v___x_600_;
    }
}
pub unsafe fn l_UInt64_instUpwardEnumerable___lam__0___boxed(
    mut v_i_601_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_i_boxed_602_: u64 = 0;
    let mut v_res_603_: *mut LeanObject = core::ptr::null_mut();
    v_i_boxed_602_ = lean_unbox_uint64(v_i_601_);
    lean_dec_ref(v_i_601_);
    v_res_603_ = l_UInt64_instUpwardEnumerable___lam__0(v_i_boxed_602_);
    return v_res_603_;
}
pub unsafe fn _init_l_UInt64_instUpwardEnumerable___lam__1___closed__0() -> *mut LeanObject {
    let mut v___x_604_: *mut LeanObject = core::ptr::null_mut();
    v___x_604_ = lean_cstr_to_nat(b"18446744073709551616\0".as_ptr().cast());
    return v___x_604_;
}
pub unsafe fn l_UInt64_instUpwardEnumerable___lam__1(
    mut v_n_605_: *mut LeanObject,
    mut v_i_606_: u64,
) -> *mut LeanObject {
    let mut v___x_607_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_608_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_609_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_610_: u8 = 0;
    v___x_607_ = lean_uint64_to_nat(v_i_606_);
    v___x_608_ = lean_nat_add(v___x_607_, v_n_605_);
    lean_dec(v___x_607_);
    v___x_609_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_UInt64_instUpwardEnumerable___lam__1___closed__0),
        core::ptr::addr_of_mut!(l_UInt64_instUpwardEnumerable___lam__1___closed__0_once),
        _init_l_UInt64_instUpwardEnumerable___lam__1___closed__0,
    );
    v___x_610_ = lean_nat_dec_lt(v___x_608_, v___x_609_);
    if v___x_610_ == 0 {
        let mut v___x_611_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v___x_608_);
        v___x_611_ = lean_box(0);
        return v___x_611_;
    } else {
        let mut v___x_612_: u64 = 0;
        let mut v___x_613_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_614_: *mut LeanObject = core::ptr::null_mut();
        v___x_612_ = lean_uint64_of_nat(v___x_608_);
        lean_dec(v___x_608_);
        v___x_613_ = lean_box_uint64(v___x_612_);
        v___x_614_ = lean_alloc_ctor(1, 1, (0) as u32);
        lean_ctor_set(v___x_614_, 0, v___x_613_);
        return v___x_614_;
    }
}
pub unsafe fn l_UInt64_instUpwardEnumerable___lam__1___boxed(
    mut v_n_615_: *mut LeanObject,
    mut v_i_616_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_i_boxed_617_: u64 = 0;
    let mut v_res_618_: *mut LeanObject = core::ptr::null_mut();
    v_i_boxed_617_ = lean_unbox_uint64(v_i_616_);
    lean_dec_ref(v_i_616_);
    v_res_618_ = l_UInt64_instUpwardEnumerable___lam__1(v_n_615_, v_i_boxed_617_);
    lean_dec(v_n_615_);
    return v_res_618_;
}
pub unsafe fn l_UInt64_instHasSize___lam__0(
    mut v_lo_630_: u64,
    mut v_hi_631_: u64,
) -> *mut LeanObject {
    let mut v___x_632_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_633_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_634_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_635_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_636_: *mut LeanObject = core::ptr::null_mut();
    v___x_632_ = lean_uint64_to_nat(v_hi_631_);
    v___x_633_ = lean_unsigned_to_nat(1);
    v___x_634_ = lean_nat_add(v___x_632_, v___x_633_);
    lean_dec(v___x_632_);
    v___x_635_ = lean_uint64_to_nat(v_lo_630_);
    v___x_636_ = lean_nat_sub(v___x_634_, v___x_635_);
    lean_dec(v___x_635_);
    lean_dec(v___x_634_);
    return v___x_636_;
}
pub unsafe fn l_UInt64_instHasSize___lam__0___boxed(
    mut v_lo_637_: *mut LeanObject,
    mut v_hi_638_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_lo_boxed_639_: u64 = 0;
    let mut v_hi_boxed_640_: u64 = 0;
    let mut v_res_641_: *mut LeanObject = core::ptr::null_mut();
    v_lo_boxed_639_ = lean_unbox_uint64(v_lo_637_);
    lean_dec_ref(v_lo_637_);
    v_hi_boxed_640_ = lean_unbox_uint64(v_hi_638_);
    lean_dec_ref(v_hi_638_);
    v_res_641_ = l_UInt64_instHasSize___lam__0(v_lo_boxed_639_, v_hi_boxed_640_);
    return v_res_641_;
}
pub unsafe fn l_UInt64_instHasSize__1___lam__0(
    mut v_lo_644_: u64,
    mut v_hi_645_: u64,
) -> *mut LeanObject {
    let mut v___x_646_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_647_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_648_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_649_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_650_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_651_: *mut LeanObject = core::ptr::null_mut();
    v___x_646_ = lean_uint64_to_nat(v_hi_645_);
    v___x_647_ = lean_unsigned_to_nat(1);
    v___x_648_ = lean_nat_add(v___x_646_, v___x_647_);
    lean_dec(v___x_646_);
    v___x_649_ = lean_uint64_to_nat(v_lo_644_);
    v___x_650_ = lean_nat_sub(v___x_648_, v___x_649_);
    lean_dec(v___x_649_);
    lean_dec(v___x_648_);
    v___x_651_ = lean_nat_sub(v___x_650_, v___x_647_);
    lean_dec(v___x_650_);
    return v___x_651_;
}
pub unsafe fn l_UInt64_instHasSize__1___lam__0___boxed(
    mut v_lo_652_: *mut LeanObject,
    mut v_hi_653_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_lo_boxed_654_: u64 = 0;
    let mut v_hi_boxed_655_: u64 = 0;
    let mut v_res_656_: *mut LeanObject = core::ptr::null_mut();
    v_lo_boxed_654_ = lean_unbox_uint64(v_lo_652_);
    lean_dec_ref(v_lo_652_);
    v_hi_boxed_655_ = lean_unbox_uint64(v_hi_653_);
    lean_dec_ref(v_hi_653_);
    v_res_656_ = l_UInt64_instHasSize__1___lam__0(v_lo_boxed_654_, v_hi_boxed_655_);
    return v_res_656_;
}
pub unsafe fn l_UInt64_instHasSize__2___lam__0(mut v_lo_659_: u64) -> *mut LeanObject {
    let mut v___x_660_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_661_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_662_: *mut LeanObject = core::ptr::null_mut();
    v___x_660_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_UInt64_instUpwardEnumerable___lam__1___closed__0),
        core::ptr::addr_of_mut!(l_UInt64_instUpwardEnumerable___lam__1___closed__0_once),
        _init_l_UInt64_instUpwardEnumerable___lam__1___closed__0,
    );
    v___x_661_ = lean_uint64_to_nat(v_lo_659_);
    v___x_662_ = lean_nat_sub(v___x_660_, v___x_661_);
    lean_dec(v___x_661_);
    return v___x_662_;
}
pub unsafe fn l_UInt64_instHasSize__2___lam__0___boxed(
    mut v_lo_663_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_lo_boxed_664_: u64 = 0;
    let mut v_res_665_: *mut LeanObject = core::ptr::null_mut();
    v_lo_boxed_664_ = lean_unbox_uint64(v_lo_663_);
    lean_dec_ref(v_lo_663_);
    v_res_665_ = l_UInt64_instHasSize__2___lam__0(v_lo_boxed_664_);
    return v_res_665_;
}
pub unsafe fn l_USize_instUpwardEnumerable___lam__0(mut v_i_668_: usize) -> *mut LeanObject {
    let mut v___x_669_: usize = 0;
    let mut v___x_670_: usize = 0;
    let mut v___x_671_: usize = 0;
    let mut v___x_672_: u8 = 0;
    v___x_669_ = 1usize;
    v___x_670_ = lean_usize_add(v_i_668_, v___x_669_);
    v___x_671_ = 0usize;
    v___x_672_ = lean_usize_dec_eq(v___x_670_, v___x_671_);
    if v___x_672_ == 0 {
        let mut v___x_673_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_674_: *mut LeanObject = core::ptr::null_mut();
        v___x_673_ = lean_box_usize(v___x_670_);
        v___x_674_ = lean_alloc_ctor(1, 1, (0) as u32);
        lean_ctor_set(v___x_674_, 0, v___x_673_);
        return v___x_674_;
    } else {
        let mut v___x_675_: *mut LeanObject = core::ptr::null_mut();
        v___x_675_ = lean_box(0);
        return v___x_675_;
    }
}
pub unsafe fn l_USize_instUpwardEnumerable___lam__0___boxed(
    mut v_i_676_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_i_boxed_677_: usize = 0;
    let mut v_res_678_: *mut LeanObject = core::ptr::null_mut();
    v_i_boxed_677_ = lean_unbox_usize(v_i_676_);
    lean_dec(v_i_676_);
    v_res_678_ = l_USize_instUpwardEnumerable___lam__0(v_i_boxed_677_);
    return v_res_678_;
}
pub unsafe fn _init_l_USize_instUpwardEnumerable___lam__1___closed__0() -> *mut LeanObject {
    let mut v___x_679_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_680_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_681_: *mut LeanObject = core::ptr::null_mut();
    v___x_679_ = l_System_Platform_numBits;
    v___x_680_ = lean_unsigned_to_nat(2);
    v___x_681_ = lean_nat_pow(v___x_680_, v___x_679_);
    return v___x_681_;
}
pub unsafe fn l_USize_instUpwardEnumerable___lam__1(
    mut v_n_682_: *mut LeanObject,
    mut v_i_683_: usize,
) -> *mut LeanObject {
    let mut v___x_684_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_685_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_686_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_687_: u8 = 0;
    v___x_684_ = lean_usize_to_nat(v_i_683_);
    v___x_685_ = lean_nat_add(v___x_684_, v_n_682_);
    lean_dec(v___x_684_);
    v___x_686_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_USize_instUpwardEnumerable___lam__1___closed__0),
        core::ptr::addr_of_mut!(l_USize_instUpwardEnumerable___lam__1___closed__0_once),
        _init_l_USize_instUpwardEnumerable___lam__1___closed__0,
    );
    v___x_687_ = lean_nat_dec_lt(v___x_685_, v___x_686_);
    if v___x_687_ == 0 {
        let mut v___x_688_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v___x_685_);
        v___x_688_ = lean_box(0);
        return v___x_688_;
    } else {
        let mut v___x_689_: usize = 0;
        let mut v___x_690_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_691_: *mut LeanObject = core::ptr::null_mut();
        v___x_689_ = lean_usize_of_nat(v___x_685_);
        lean_dec(v___x_685_);
        v___x_690_ = lean_box_usize(v___x_689_);
        v___x_691_ = lean_alloc_ctor(1, 1, (0) as u32);
        lean_ctor_set(v___x_691_, 0, v___x_690_);
        return v___x_691_;
    }
}
pub unsafe fn l_USize_instUpwardEnumerable___lam__1___boxed(
    mut v_n_692_: *mut LeanObject,
    mut v_i_693_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_i_boxed_694_: usize = 0;
    let mut v_res_695_: *mut LeanObject = core::ptr::null_mut();
    v_i_boxed_694_ = lean_unbox_usize(v_i_693_);
    lean_dec(v_i_693_);
    v_res_695_ = l_USize_instUpwardEnumerable___lam__1(v_n_692_, v_i_boxed_694_);
    lean_dec(v_n_692_);
    return v_res_695_;
}
pub unsafe fn l_USize_instHasSize___lam__0(
    mut v_lo_707_: usize,
    mut v_hi_708_: usize,
) -> *mut LeanObject {
    let mut v___x_709_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_710_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_711_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_712_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_713_: *mut LeanObject = core::ptr::null_mut();
    v___x_709_ = lean_usize_to_nat(v_hi_708_);
    v___x_710_ = lean_unsigned_to_nat(1);
    v___x_711_ = lean_nat_add(v___x_709_, v___x_710_);
    lean_dec(v___x_709_);
    v___x_712_ = lean_usize_to_nat(v_lo_707_);
    v___x_713_ = lean_nat_sub(v___x_711_, v___x_712_);
    lean_dec(v___x_712_);
    lean_dec(v___x_711_);
    return v___x_713_;
}
pub unsafe fn l_USize_instHasSize___lam__0___boxed(
    mut v_lo_714_: *mut LeanObject,
    mut v_hi_715_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_lo_boxed_716_: usize = 0;
    let mut v_hi_boxed_717_: usize = 0;
    let mut v_res_718_: *mut LeanObject = core::ptr::null_mut();
    v_lo_boxed_716_ = lean_unbox_usize(v_lo_714_);
    lean_dec(v_lo_714_);
    v_hi_boxed_717_ = lean_unbox_usize(v_hi_715_);
    lean_dec(v_hi_715_);
    v_res_718_ = l_USize_instHasSize___lam__0(v_lo_boxed_716_, v_hi_boxed_717_);
    return v_res_718_;
}
pub unsafe fn l_USize_instHasSize__1___lam__0(
    mut v_lo_721_: usize,
    mut v_hi_722_: usize,
) -> *mut LeanObject {
    let mut v___x_723_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_724_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_725_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_726_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_727_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_728_: *mut LeanObject = core::ptr::null_mut();
    v___x_723_ = lean_usize_to_nat(v_hi_722_);
    v___x_724_ = lean_unsigned_to_nat(1);
    v___x_725_ = lean_nat_add(v___x_723_, v___x_724_);
    lean_dec(v___x_723_);
    v___x_726_ = lean_usize_to_nat(v_lo_721_);
    v___x_727_ = lean_nat_sub(v___x_725_, v___x_726_);
    lean_dec(v___x_726_);
    lean_dec(v___x_725_);
    v___x_728_ = lean_nat_sub(v___x_727_, v___x_724_);
    lean_dec(v___x_727_);
    return v___x_728_;
}
pub unsafe fn l_USize_instHasSize__1___lam__0___boxed(
    mut v_lo_729_: *mut LeanObject,
    mut v_hi_730_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_lo_boxed_731_: usize = 0;
    let mut v_hi_boxed_732_: usize = 0;
    let mut v_res_733_: *mut LeanObject = core::ptr::null_mut();
    v_lo_boxed_731_ = lean_unbox_usize(v_lo_729_);
    lean_dec(v_lo_729_);
    v_hi_boxed_732_ = lean_unbox_usize(v_hi_730_);
    lean_dec(v_hi_730_);
    v_res_733_ = l_USize_instHasSize__1___lam__0(v_lo_boxed_731_, v_hi_boxed_732_);
    return v_res_733_;
}
pub unsafe fn l_USize_instHasSize__2___lam__0(mut v_lo_736_: usize) -> *mut LeanObject {
    let mut v___x_737_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_738_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_739_: *mut LeanObject = core::ptr::null_mut();
    v___x_737_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_USize_instUpwardEnumerable___lam__1___closed__0),
        core::ptr::addr_of_mut!(l_USize_instUpwardEnumerable___lam__1___closed__0_once),
        _init_l_USize_instUpwardEnumerable___lam__1___closed__0,
    );
    v___x_738_ = lean_usize_to_nat(v_lo_736_);
    v___x_739_ = lean_nat_sub(v___x_737_, v___x_738_);
    lean_dec(v___x_738_);
    return v___x_739_;
}
pub unsafe fn l_USize_instHasSize__2___lam__0___boxed(
    mut v_lo_740_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_lo_boxed_741_: usize = 0;
    let mut v_res_742_: *mut LeanObject = core::ptr::null_mut();
    v_lo_boxed_741_ = lean_unbox_usize(v_lo_740_);
    lean_dec(v_lo_740_);
    v_res_742_ = l_USize_instHasSize__2___lam__0(v_lo_boxed_741_);
    return v_res_742_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Init_Data_Range_Polymorphic_UInt(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Init_Data_Range_Polymorphic_BitVec(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_UInt(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_ByCases(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_BitVec_Lemmas(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Option_Lemmas(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    l_UInt32_instLeast_x3f___closed__0___boxed__const__1 =
        _init_l_UInt32_instLeast_x3f___closed__0___boxed__const__1();
    lean_mark_persistent(l_UInt32_instLeast_x3f___closed__0___boxed__const__1);
    l_UInt32_instLeast_x3f = _init_l_UInt32_instLeast_x3f();
    lean_mark_persistent(l_UInt32_instLeast_x3f);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Init_Data_Range_Polymorphic_UInt(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_meta_initialized = true;
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Init_Data_Range_Polymorphic_UInt(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Init_Data_Range_Polymorphic_BitVec(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Data_UInt(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_ByCases(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Data_BitVec_Lemmas(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Data_Option_Lemmas(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Range_Polymorphic_UInt(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = meta_initialize_Init_Data_Range_Polymorphic_UInt(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_Init_Data_Range_Polymorphic_UInt(builtin);
}
