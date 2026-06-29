// Lean compiler output
// Module: Lean.Data.RBMap
// Imports: Init.Data.Ord.Basic Init.Data.Nat.Linear Init.Data.Array.Basic Init.WFTactics
use crate::r#gen::Init::Control::Id::{
    l_Id_instMonad___lam__0, l_Id_instMonad___lam__1___boxed, l_Id_instMonad___lam__2___boxed,
    l_Id_instMonad___lam__3, l_Id_instMonad___lam__4___boxed, l_Id_instMonad___lam__5___boxed,
    l_Id_instMonad___lam__6,
};
use crate::r#gen::Init::Data::Array::Basic::{
    initialize_Init_Data_Array_Basic, l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold,
    runtime_initialize_Init_Data_Array_Basic,
};
use crate::r#gen::Init::Data::Nat::Linear::{
    initialize_Init_Data_Nat_Linear, runtime_initialize_Init_Data_Nat_Linear,
};
use crate::r#gen::Init::Data::Ord::Basic::{
    initialize_Init_Data_Ord_Basic, runtime_initialize_Init_Data_Ord_Basic,
};
use crate::r#gen::Init::Data::Repr::{
    l_List_repr___redArg, l_Prod_repr___boxed, l_Repr_addAppParen,
    l_instReprTupleOfRepr___redArg___lam__0,
};
use crate::r#gen::Init::Prelude::{l_List_foldl___redArg, l_panic___redArg};
use crate::r#gen::Init::Util::l_mkPanicMessageWithDecl;
use crate::r#gen::Init::WFTactics::{initialize_Init_WFTactics, runtime_initialize_Init_WFTactics};
use crate::lean_imports_rs::Init::Data::UInt::BasicAux::lean_usize_of_nat;
use crate::lean_imports_rs::Init::Prelude::{
    lean_array_get_size, lean_array_push, lean_nat_add, lean_nat_dec_le, lean_nat_dec_lt,
};
pub static l_Lean_RBNode_toArray___redArg___closed__0_value: crate::leanh::LeanArrayObject<0> =
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
static mut l_Lean_RBNode_toArray___redArg___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_RBNode_toArray___redArg___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_RBMap_toList___redArg___closed__0_value: crate::leanh::LeanClosureObject<0> =
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
        m_fun: l_Lean_RBMap_toList___redArg___lam__0 as *const core::ffi::c_void,
        m_arity: 3,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_RBMap_toList___redArg___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_RBMap_toList___redArg___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_RBMap_toArray___redArg___closed__0_value: crate::leanh::LeanClosureObject<0> =
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
        m_fun: l_Lean_RBMap_toArray___redArg___lam__0 as *const core::ffi::c_void,
        m_arity: 3,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_RBMap_toArray___redArg___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_RBMap_toArray___redArg___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_RBMap_toArray___redArg___closed__1_value: crate::leanh::LeanArrayObject<0> =
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
static mut l_Lean_RBMap_toArray___redArg___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_RBMap_toArray___redArg___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_RBMap_instRepr___redArg___lam__0___closed__0_value:
    crate::leanh::LeanStringObject<14> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 14,
    m_capacity: 14,
    m_length: 13,
    m_data: [76, 101, 97, 110, 46, 114, 98, 109, 97, 112, 79, 102, 32, 0],
};
static mut l_Lean_RBMap_instRepr___redArg___lam__0___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_RBMap_instRepr___redArg___lam__0___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_RBMap_instRepr___redArg___lam__0___closed__1_value: crate::leanh::LeanCtorObject<
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
        core::ptr::addr_of!(l_Lean_RBMap_instRepr___redArg___lam__0___closed__0_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_RBMap_instRepr___redArg___lam__0___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_RBMap_instRepr___redArg___lam__0___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_RBMap_fromArray___redArg___closed__0_value: crate::leanh::LeanClosureObject<0> =
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
        m_fun: l_Id_instMonad___lam__0 as *const core::ffi::c_void,
        m_arity: 4,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_RBMap_fromArray___redArg___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_RBMap_fromArray___redArg___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_RBMap_fromArray___redArg___closed__1_value: crate::leanh::LeanClosureObject<0> =
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
        m_fun: l_Id_instMonad___lam__1___boxed as *const core::ffi::c_void,
        m_arity: 4,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_RBMap_fromArray___redArg___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_RBMap_fromArray___redArg___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_RBMap_fromArray___redArg___closed__2_value: crate::leanh::LeanClosureObject<0> =
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
        m_fun: l_Id_instMonad___lam__2___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_RBMap_fromArray___redArg___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_RBMap_fromArray___redArg___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_RBMap_fromArray___redArg___closed__3_value: crate::leanh::LeanClosureObject<0> =
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
        m_fun: l_Id_instMonad___lam__3 as *const core::ffi::c_void,
        m_arity: 4,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_RBMap_fromArray___redArg___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_RBMap_fromArray___redArg___closed__3_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_RBMap_fromArray___redArg___closed__4_value: crate::leanh::LeanClosureObject<0> =
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
        m_fun: l_Id_instMonad___lam__4___boxed as *const core::ffi::c_void,
        m_arity: 4,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_RBMap_fromArray___redArg___closed__4: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_RBMap_fromArray___redArg___closed__4_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_RBMap_fromArray___redArg___closed__5_value: crate::leanh::LeanClosureObject<0> =
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
        m_fun: l_Id_instMonad___lam__5___boxed as *const core::ffi::c_void,
        m_arity: 4,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_RBMap_fromArray___redArg___closed__5: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_RBMap_fromArray___redArg___closed__5_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_RBMap_fromArray___redArg___closed__6_value: crate::leanh::LeanClosureObject<0> =
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
        m_fun: l_Id_instMonad___lam__6 as *const core::ffi::c_void,
        m_arity: 4,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_RBMap_fromArray___redArg___closed__6: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_RBMap_fromArray___redArg___closed__6_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_RBMap_fromArray___redArg___closed__7_value: crate::leanh::LeanCtorObject<2> =
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
            core::ptr::addr_of!(l_Lean_RBMap_fromArray___redArg___closed__0_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_RBMap_fromArray___redArg___closed__1_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_RBMap_fromArray___redArg___closed__7: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_RBMap_fromArray___redArg___closed__7_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_RBMap_fromArray___redArg___closed__8_value: crate::leanh::LeanCtorObject<5> =
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
            core::ptr::addr_of!(l_Lean_RBMap_fromArray___redArg___closed__7_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_RBMap_fromArray___redArg___closed__2_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_RBMap_fromArray___redArg___closed__3_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_RBMap_fromArray___redArg___closed__4_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_RBMap_fromArray___redArg___closed__5_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_RBMap_fromArray___redArg___closed__8: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_RBMap_fromArray___redArg___closed__8_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_RBMap_fromArray___redArg___closed__9_value: crate::leanh::LeanCtorObject<2> =
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
            core::ptr::addr_of!(l_Lean_RBMap_fromArray___redArg___closed__8_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_RBMap_fromArray___redArg___closed__6_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_RBMap_fromArray___redArg___closed__9: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_RBMap_fromArray___redArg___closed__9_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_RBMap_maxDepth___redArg___closed__0_value: crate::leanh::LeanClosureObject<0> =
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
        m_fun: l_Lean_RBMap_maxDepth___redArg___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_RBMap_maxDepth___redArg___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_RBMap_maxDepth___redArg___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_RBMap_min_x21___redArg___closed__0_value: crate::leanh::LeanStringObject<16> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 16,
        m_capacity: 16,
        m_length: 15,
        m_data: [
            76, 101, 97, 110, 46, 68, 97, 116, 97, 46, 82, 66, 77, 97, 112, 0,
        ],
    };
static mut l_Lean_RBMap_min_x21___redArg___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_RBMap_min_x21___redArg___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_RBMap_min_x21___redArg___closed__1_value: crate::leanh::LeanStringObject<16> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 16,
        m_capacity: 16,
        m_length: 15,
        m_data: [
            76, 101, 97, 110, 46, 82, 66, 77, 97, 112, 46, 109, 105, 110, 33, 0,
        ],
    };
static mut l_Lean_RBMap_min_x21___redArg___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_RBMap_min_x21___redArg___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_RBMap_min_x21___redArg___closed__2_value: crate::leanh::LeanStringObject<13> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 13,
        m_capacity: 13,
        m_length: 12,
        m_data: [109, 97, 112, 32, 105, 115, 32, 101, 109, 112, 116, 121, 0],
    };
static mut l_Lean_RBMap_min_x21___redArg___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_RBMap_min_x21___redArg___closed__2_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_RBMap_min_x21___redArg___closed__3_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_RBMap_min_x21___redArg___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_RBMap_max_x21___redArg___closed__0_value: crate::leanh::LeanStringObject<16> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 16,
        m_capacity: 16,
        m_length: 15,
        m_data: [
            76, 101, 97, 110, 46, 82, 66, 77, 97, 112, 46, 109, 97, 120, 33, 0,
        ],
    };
static mut l_Lean_RBMap_max_x21___redArg___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_RBMap_max_x21___redArg___closed__0_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_RBMap_max_x21___redArg___closed__1_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_RBMap_max_x21___redArg___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_RBMap_find_x21___redArg___closed__0_value: crate::leanh::LeanStringObject<17> =
    crate::leanh::LeanStringObject {
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
            76, 101, 97, 110, 46, 82, 66, 77, 97, 112, 46, 102, 105, 110, 100, 33, 0,
        ],
    };
static mut l_Lean_RBMap_find_x21___redArg___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_RBMap_find_x21___redArg___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_RBMap_find_x21___redArg___closed__1_value: crate::leanh::LeanStringObject<22> =
    crate::leanh::LeanStringObject {
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
            107, 101, 121, 32, 105, 115, 32, 110, 111, 116, 32, 105, 110, 32, 116, 104, 101, 32,
            109, 97, 112, 0,
        ],
    };
static mut l_Lean_RBMap_find_x21___redArg___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_RBMap_find_x21___redArg___closed__1_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_RBMap_find_x21___redArg___closed__2_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_RBMap_find_x21___redArg___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub unsafe fn l_Lean_RBColor_ctorIdx(mut v_x_3027_: u8) -> *mut crate::leanh::LeanObject {
    if v_x_3027_ == 0 {
        let mut v___x_3028_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_3028_ = crate::leanh::lean_unsigned_to_nat(0);
        return v___x_3028_;
    } else {
        let mut v___x_3029_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_3029_ = crate::leanh::lean_unsigned_to_nat(1);
        return v___x_3029_;
    }
}
pub unsafe fn l_Lean_RBColor_ctorIdx___boxed(
    mut v_x_3030_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_x_boxed_3031_: u8 = 0;
    let mut v_res_3032_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_x_boxed_3031_ = (crate::leanh::lean_unbox(v_x_3030_) as u8);
    v_res_3032_ = l_Lean_RBColor_ctorIdx(v_x_boxed_3031_);
    return v_res_3032_;
}
pub unsafe fn l_Lean_RBColor_toCtorIdx(mut v_x_3033_: u8) -> *mut crate::leanh::LeanObject {
    let mut v___x_3034_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3034_ = l_Lean_RBColor_ctorIdx(v_x_3033_);
    return v___x_3034_;
}
pub unsafe fn l_Lean_RBColor_toCtorIdx___boxed(
    mut v_x_3035_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_x_4__boxed_3036_: u8 = 0;
    let mut v_res_3037_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_x_4__boxed_3036_ = (crate::leanh::lean_unbox(v_x_3035_) as u8);
    v_res_3037_ = l_Lean_RBColor_toCtorIdx(v_x_4__boxed_3036_);
    return v_res_3037_;
}
pub unsafe fn l_Lean_RBColor_ctorElim___redArg(
    mut v_k_3038_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc(v_k_3038_);
    return v_k_3038_;
}
pub unsafe fn l_Lean_RBColor_ctorElim___redArg___boxed(
    mut v_k_3039_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3040_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3040_ = l_Lean_RBColor_ctorElim___redArg(v_k_3039_);
    crate::leanh::lean_dec(v_k_3039_);
    return v_res_3040_;
}
pub unsafe fn l_Lean_RBColor_ctorElim(
    mut v_motive_3041_: *mut crate::leanh::LeanObject,
    mut v_ctorIdx_3042_: *mut crate::leanh::LeanObject,
    mut v_t_3043_: u8,
    mut v_h_3044_: *mut crate::leanh::LeanObject,
    mut v_k_3045_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc(v_k_3045_);
    return v_k_3045_;
}
pub unsafe fn l_Lean_RBColor_ctorElim___boxed(
    mut v_motive_3046_: *mut crate::leanh::LeanObject,
    mut v_ctorIdx_3047_: *mut crate::leanh::LeanObject,
    mut v_t_3048_: *mut crate::leanh::LeanObject,
    mut v_h_3049_: *mut crate::leanh::LeanObject,
    mut v_k_3050_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_t_boxed_3051_: u8 = 0;
    let mut v_res_3052_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_t_boxed_3051_ = (crate::leanh::lean_unbox(v_t_3048_) as u8);
    v_res_3052_ = l_Lean_RBColor_ctorElim(
        v_motive_3046_,
        v_ctorIdx_3047_,
        v_t_boxed_3051_,
        v_h_3049_,
        v_k_3050_,
    );
    crate::leanh::lean_dec(v_k_3050_);
    crate::leanh::lean_dec(v_ctorIdx_3047_);
    return v_res_3052_;
}
pub unsafe fn l_Lean_RBColor_red_elim___redArg(
    mut v_red_3053_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc(v_red_3053_);
    return v_red_3053_;
}
pub unsafe fn l_Lean_RBColor_red_elim___redArg___boxed(
    mut v_red_3054_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3055_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3055_ = l_Lean_RBColor_red_elim___redArg(v_red_3054_);
    crate::leanh::lean_dec(v_red_3054_);
    return v_res_3055_;
}
pub unsafe fn l_Lean_RBColor_red_elim(
    mut v_motive_3056_: *mut crate::leanh::LeanObject,
    mut v_t_3057_: u8,
    mut v_h_3058_: *mut crate::leanh::LeanObject,
    mut v_red_3059_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc(v_red_3059_);
    return v_red_3059_;
}
pub unsafe fn l_Lean_RBColor_red_elim___boxed(
    mut v_motive_3060_: *mut crate::leanh::LeanObject,
    mut v_t_3061_: *mut crate::leanh::LeanObject,
    mut v_h_3062_: *mut crate::leanh::LeanObject,
    mut v_red_3063_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_t_boxed_3064_: u8 = 0;
    let mut v_res_3065_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_t_boxed_3064_ = (crate::leanh::lean_unbox(v_t_3061_) as u8);
    v_res_3065_ = l_Lean_RBColor_red_elim(v_motive_3060_, v_t_boxed_3064_, v_h_3062_, v_red_3063_);
    crate::leanh::lean_dec(v_red_3063_);
    return v_res_3065_;
}
pub unsafe fn l_Lean_RBColor_black_elim___redArg(
    mut v_black_3066_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc(v_black_3066_);
    return v_black_3066_;
}
pub unsafe fn l_Lean_RBColor_black_elim___redArg___boxed(
    mut v_black_3067_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3068_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3068_ = l_Lean_RBColor_black_elim___redArg(v_black_3067_);
    crate::leanh::lean_dec(v_black_3067_);
    return v_res_3068_;
}
pub unsafe fn l_Lean_RBColor_black_elim(
    mut v_motive_3069_: *mut crate::leanh::LeanObject,
    mut v_t_3070_: u8,
    mut v_h_3071_: *mut crate::leanh::LeanObject,
    mut v_black_3072_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc(v_black_3072_);
    return v_black_3072_;
}
pub unsafe fn l_Lean_RBColor_black_elim___boxed(
    mut v_motive_3073_: *mut crate::leanh::LeanObject,
    mut v_t_3074_: *mut crate::leanh::LeanObject,
    mut v_h_3075_: *mut crate::leanh::LeanObject,
    mut v_black_3076_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_t_boxed_3077_: u8 = 0;
    let mut v_res_3078_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_t_boxed_3077_ = (crate::leanh::lean_unbox(v_t_3074_) as u8);
    v_res_3078_ =
        l_Lean_RBColor_black_elim(v_motive_3073_, v_t_boxed_3077_, v_h_3075_, v_black_3076_);
    crate::leanh::lean_dec(v_black_3076_);
    return v_res_3078_;
}
pub unsafe fn l_Lean_RBNode_ctorIdx___redArg(
    mut v_x_3079_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_3079_) == 0 {
        let mut v___x_3080_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_3080_ = crate::leanh::lean_unsigned_to_nat(0);
        return v___x_3080_;
    } else {
        let mut v___x_3081_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_3081_ = crate::leanh::lean_unsigned_to_nat(1);
        return v___x_3081_;
    }
}
pub unsafe fn l_Lean_RBNode_ctorIdx___redArg___boxed(
    mut v_x_3082_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3083_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3083_ = l_Lean_RBNode_ctorIdx___redArg(v_x_3082_);
    crate::leanh::lean_dec(v_x_3082_);
    return v_res_3083_;
}
pub unsafe fn l_Lean_RBNode_ctorIdx(
    mut v_00_u03b1_3084_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_3085_: *mut crate::leanh::LeanObject,
    mut v_x_3086_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3087_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3087_ = l_Lean_RBNode_ctorIdx___redArg(v_x_3086_);
    return v___x_3087_;
}
pub unsafe fn l_Lean_RBNode_ctorIdx___boxed(
    mut v_00_u03b1_3088_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_3089_: *mut crate::leanh::LeanObject,
    mut v_x_3090_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3091_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3091_ = l_Lean_RBNode_ctorIdx(v_00_u03b1_3088_, v_00_u03b2_3089_, v_x_3090_);
    crate::leanh::lean_dec(v_x_3090_);
    return v_res_3091_;
}
pub unsafe fn l_Lean_RBNode_ctorElim___redArg(
    mut v_t_3092_: *mut crate::leanh::LeanObject,
    mut v_k_3093_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_t_3092_) == 0 {
        return v_k_3093_;
    } else {
        let mut v_color_3094_: u8 = 0;
        let mut v_lchild_3095_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_key_3096_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_val_3097_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_rchild_3098_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3099_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3100_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_color_3094_ = crate::leanh::lean_ctor_get_uint8(
            v_t_3092_,
            (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 4) as u32,
        );
        v_lchild_3095_ = crate::leanh::lean_ctor_get(v_t_3092_, 0);
        crate::leanh::lean_inc(v_lchild_3095_);
        v_key_3096_ = crate::leanh::lean_ctor_get(v_t_3092_, 1);
        crate::leanh::lean_inc(v_key_3096_);
        v_val_3097_ = crate::leanh::lean_ctor_get(v_t_3092_, 2);
        crate::leanh::lean_inc(v_val_3097_);
        v_rchild_3098_ = crate::leanh::lean_ctor_get(v_t_3092_, 3);
        crate::leanh::lean_inc(v_rchild_3098_);
        crate::leanh::lean_dec_ref_known(v_t_3092_, 4);
        v___x_3099_ = crate::leanh::lean_box((v_color_3094_) as usize);
        v___x_3100_ = crate::leanh::lean_apply_5(
            v_k_3093_,
            v___x_3099_,
            v_lchild_3095_,
            v_key_3096_,
            v_val_3097_,
            v_rchild_3098_,
        );
        return v___x_3100_;
    }
}
pub unsafe fn l_Lean_RBNode_ctorElim(
    mut v_00_u03b1_3101_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_3102_: *mut crate::leanh::LeanObject,
    mut v_motive_3103_: *mut crate::leanh::LeanObject,
    mut v_ctorIdx_3104_: *mut crate::leanh::LeanObject,
    mut v_t_3105_: *mut crate::leanh::LeanObject,
    mut v_h_3106_: *mut crate::leanh::LeanObject,
    mut v_k_3107_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3108_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3108_ = l_Lean_RBNode_ctorElim___redArg(v_t_3105_, v_k_3107_);
    return v___x_3108_;
}
pub unsafe fn l_Lean_RBNode_ctorElim___boxed(
    mut v_00_u03b1_3109_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_3110_: *mut crate::leanh::LeanObject,
    mut v_motive_3111_: *mut crate::leanh::LeanObject,
    mut v_ctorIdx_3112_: *mut crate::leanh::LeanObject,
    mut v_t_3113_: *mut crate::leanh::LeanObject,
    mut v_h_3114_: *mut crate::leanh::LeanObject,
    mut v_k_3115_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3116_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3116_ = l_Lean_RBNode_ctorElim(
        v_00_u03b1_3109_,
        v_00_u03b2_3110_,
        v_motive_3111_,
        v_ctorIdx_3112_,
        v_t_3113_,
        v_h_3114_,
        v_k_3115_,
    );
    crate::leanh::lean_dec(v_ctorIdx_3112_);
    return v_res_3116_;
}
pub unsafe fn l_Lean_RBNode_leaf_elim___redArg(
    mut v_t_3117_: *mut crate::leanh::LeanObject,
    mut v_leaf_3118_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3119_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3119_ = l_Lean_RBNode_ctorElim___redArg(v_t_3117_, v_leaf_3118_);
    return v___x_3119_;
}
pub unsafe fn l_Lean_RBNode_leaf_elim(
    mut v_00_u03b1_3120_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_3121_: *mut crate::leanh::LeanObject,
    mut v_motive_3122_: *mut crate::leanh::LeanObject,
    mut v_t_3123_: *mut crate::leanh::LeanObject,
    mut v_h_3124_: *mut crate::leanh::LeanObject,
    mut v_leaf_3125_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3126_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3126_ = l_Lean_RBNode_ctorElim___redArg(v_t_3123_, v_leaf_3125_);
    return v___x_3126_;
}
pub unsafe fn l_Lean_RBNode_node_elim___redArg(
    mut v_t_3127_: *mut crate::leanh::LeanObject,
    mut v_node_3128_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3129_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3129_ = l_Lean_RBNode_ctorElim___redArg(v_t_3127_, v_node_3128_);
    return v___x_3129_;
}
pub unsafe fn l_Lean_RBNode_node_elim(
    mut v_00_u03b1_3130_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_3131_: *mut crate::leanh::LeanObject,
    mut v_motive_3132_: *mut crate::leanh::LeanObject,
    mut v_t_3133_: *mut crate::leanh::LeanObject,
    mut v_h_3134_: *mut crate::leanh::LeanObject,
    mut v_node_3135_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3136_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3136_ = l_Lean_RBNode_ctorElim___redArg(v_t_3133_, v_node_3135_);
    return v___x_3136_;
}
pub unsafe fn l_Lean_RBNode_depth___redArg(
    mut v_f_3137_: *mut crate::leanh::LeanObject,
    mut v_x_3138_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_3138_) == 0 {
        let mut v___x_3139_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec_ref(v_f_3137_);
        v___x_3139_ = crate::leanh::lean_unsigned_to_nat(0);
        return v___x_3139_;
    } else {
        let mut v_lchild_3140_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_rchild_3141_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3142_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3143_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3144_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3145_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3146_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_lchild_3140_ = crate::leanh::lean_ctor_get(v_x_3138_, 0);
        v_rchild_3141_ = crate::leanh::lean_ctor_get(v_x_3138_, 3);
        crate::leanh::lean_inc_ref_n(v_f_3137_, 2);
        v___x_3142_ = l_Lean_RBNode_depth___redArg(v_f_3137_, v_lchild_3140_);
        v___x_3143_ = l_Lean_RBNode_depth___redArg(v_f_3137_, v_rchild_3141_);
        v___x_3144_ = crate::leanh::lean_apply_2(v_f_3137_, v___x_3142_, v___x_3143_);
        v___x_3145_ = crate::leanh::lean_unsigned_to_nat(1);
        v___x_3146_ = lean_nat_add(v___x_3144_, v___x_3145_);
        crate::leanh::lean_dec(v___x_3144_);
        return v___x_3146_;
    }
}
pub unsafe fn l_Lean_RBNode_depth___redArg___boxed(
    mut v_f_3147_: *mut crate::leanh::LeanObject,
    mut v_x_3148_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3149_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3149_ = l_Lean_RBNode_depth___redArg(v_f_3147_, v_x_3148_);
    crate::leanh::lean_dec(v_x_3148_);
    return v_res_3149_;
}
pub unsafe fn l_Lean_RBNode_depth(
    mut v_00_u03b1_3150_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_3151_: *mut crate::leanh::LeanObject,
    mut v_f_3152_: *mut crate::leanh::LeanObject,
    mut v_x_3153_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3154_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3154_ = l_Lean_RBNode_depth___redArg(v_f_3152_, v_x_3153_);
    return v___x_3154_;
}
pub unsafe fn l_Lean_RBNode_depth___boxed(
    mut v_00_u03b1_3155_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_3156_: *mut crate::leanh::LeanObject,
    mut v_f_3157_: *mut crate::leanh::LeanObject,
    mut v_x_3158_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3159_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3159_ = l_Lean_RBNode_depth(v_00_u03b1_3155_, v_00_u03b2_3156_, v_f_3157_, v_x_3158_);
    crate::leanh::lean_dec(v_x_3158_);
    return v_res_3159_;
}
pub unsafe fn l_Lean_RBNode_min___redArg(
    mut v_x_3160_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3161_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_lchild_3162_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_key_3163_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_3164_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3165_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3166_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_3160_) == 0 {
                    v___x_3161_ = crate::leanh::lean_box(0);
                    return v___x_3161_;
                } else {
                    v_lchild_3162_ = crate::leanh::lean_ctor_get(v_x_3160_, 0);
                    if crate::leanh::lean_obj_tag(v_lchild_3162_) == 0 {
                        v_key_3163_ = crate::leanh::lean_ctor_get(v_x_3160_, 1);
                        v_val_3164_ = crate::leanh::lean_ctor_get(v_x_3160_, 2);
                        crate::leanh::lean_inc(v_val_3164_);
                        crate::leanh::lean_inc(v_key_3163_);
                        v___x_3165_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_3165_, 0, v_key_3163_);
                        crate::leanh::lean_ctor_set(v___x_3165_, 1, v_val_3164_);
                        v___x_3166_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_3166_, 0, v___x_3165_);
                        return v___x_3166_;
                    } else {
                        v_x_3160_ = v_lchild_3162_;
                        state = 0;
                        continue;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_RBNode_min___redArg___boxed(
    mut v_x_3168_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3169_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3169_ = l_Lean_RBNode_min___redArg(v_x_3168_);
    crate::leanh::lean_dec(v_x_3168_);
    return v_res_3169_;
}
pub unsafe fn l_Lean_RBNode_min(
    mut v_00_u03b1_3170_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_3171_: *mut crate::leanh::LeanObject,
    mut v_x_3172_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3173_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3173_ = l_Lean_RBNode_min___redArg(v_x_3172_);
    return v___x_3173_;
}
pub unsafe fn l_Lean_RBNode_min___boxed(
    mut v_00_u03b1_3174_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_3175_: *mut crate::leanh::LeanObject,
    mut v_x_3176_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3177_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3177_ = l_Lean_RBNode_min(v_00_u03b1_3174_, v_00_u03b2_3175_, v_x_3176_);
    crate::leanh::lean_dec(v_x_3176_);
    return v_res_3177_;
}
pub unsafe fn l_Lean_RBNode_max___redArg(
    mut v_x_3178_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3179_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_rchild_3180_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_key_3181_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_3182_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3183_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3184_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_3178_) == 0 {
                    v___x_3179_ = crate::leanh::lean_box(0);
                    return v___x_3179_;
                } else {
                    v_rchild_3180_ = crate::leanh::lean_ctor_get(v_x_3178_, 3);
                    if crate::leanh::lean_obj_tag(v_rchild_3180_) == 0 {
                        v_key_3181_ = crate::leanh::lean_ctor_get(v_x_3178_, 1);
                        v_val_3182_ = crate::leanh::lean_ctor_get(v_x_3178_, 2);
                        crate::leanh::lean_inc(v_val_3182_);
                        crate::leanh::lean_inc(v_key_3181_);
                        v___x_3183_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_3183_, 0, v_key_3181_);
                        crate::leanh::lean_ctor_set(v___x_3183_, 1, v_val_3182_);
                        v___x_3184_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_3184_, 0, v___x_3183_);
                        return v___x_3184_;
                    } else {
                        v_x_3178_ = v_rchild_3180_;
                        state = 0;
                        continue;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_RBNode_max___redArg___boxed(
    mut v_x_3186_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3187_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3187_ = l_Lean_RBNode_max___redArg(v_x_3186_);
    crate::leanh::lean_dec(v_x_3186_);
    return v_res_3187_;
}
pub unsafe fn l_Lean_RBNode_max(
    mut v_00_u03b1_3188_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_3189_: *mut crate::leanh::LeanObject,
    mut v_x_3190_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3191_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3191_ = l_Lean_RBNode_max___redArg(v_x_3190_);
    return v___x_3191_;
}
pub unsafe fn l_Lean_RBNode_max___boxed(
    mut v_00_u03b1_3192_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_3193_: *mut crate::leanh::LeanObject,
    mut v_x_3194_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3195_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3195_ = l_Lean_RBNode_max(v_00_u03b1_3192_, v_00_u03b2_3193_, v_x_3194_);
    crate::leanh::lean_dec(v_x_3194_);
    return v_res_3195_;
}
pub unsafe fn l_Lean_RBNode_fold___redArg(
    mut v_f_3196_: *mut crate::leanh::LeanObject,
    mut v_x_3197_: *mut crate::leanh::LeanObject,
    mut v_x_3198_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_lchild_3199_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_key_3200_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_3201_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_rchild_3202_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3203_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3204_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_3198_) == 0 {
                    crate::leanh::lean_dec(v_f_3196_);
                    return v_x_3197_;
                } else {
                    v_lchild_3199_ = crate::leanh::lean_ctor_get(v_x_3198_, 0);
                    crate::leanh::lean_inc(v_lchild_3199_);
                    v_key_3200_ = crate::leanh::lean_ctor_get(v_x_3198_, 1);
                    crate::leanh::lean_inc(v_key_3200_);
                    v_val_3201_ = crate::leanh::lean_ctor_get(v_x_3198_, 2);
                    crate::leanh::lean_inc(v_val_3201_);
                    v_rchild_3202_ = crate::leanh::lean_ctor_get(v_x_3198_, 3);
                    crate::leanh::lean_inc(v_rchild_3202_);
                    crate::leanh::lean_dec_ref_known(v_x_3198_, 4);
                    crate::leanh::lean_inc_n(v_f_3196_, 2);
                    v___x_3203_ = l_Lean_RBNode_fold___redArg(v_f_3196_, v_x_3197_, v_lchild_3199_);
                    v___x_3204_ = crate::leanh::lean_apply_3(
                        v_f_3196_,
                        v___x_3203_,
                        v_key_3200_,
                        v_val_3201_,
                    );
                    v_x_3197_ = v___x_3204_;
                    v_x_3198_ = v_rchild_3202_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_RBNode_fold(
    mut v_00_u03b1_3206_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_3207_: *mut crate::leanh::LeanObject,
    mut v_00_u03c3_3208_: *mut crate::leanh::LeanObject,
    mut v_f_3209_: *mut crate::leanh::LeanObject,
    mut v_x_3210_: *mut crate::leanh::LeanObject,
    mut v_x_3211_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3212_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3212_ = l_Lean_RBNode_fold___redArg(v_f_3209_, v_x_3210_, v_x_3211_);
    return v___x_3212_;
}
pub unsafe fn l_Lean_RBNode_forM___redArg___lam__1(
    mut v_f_3213_: *mut crate::leanh::LeanObject,
    mut v_key_3214_: *mut crate::leanh::LeanObject,
    mut v_val_3215_: *mut crate::leanh::LeanObject,
    mut v_toBind_3216_: *mut crate::leanh::LeanObject,
    mut v___f_3217_: *mut crate::leanh::LeanObject,
    mut v_____r_3218_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3219_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3220_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3219_ = crate::leanh::lean_apply_2(v_f_3213_, v_key_3214_, v_val_3215_);
    v___x_3220_ = crate::leanh::lean_apply_4(
        v_toBind_3216_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___x_3219_,
        v___f_3217_,
    );
    return v___x_3220_;
}
pub unsafe fn l_Lean_RBNode_forM___redArg(
    mut v_inst_3221_: *mut crate::leanh::LeanObject,
    mut v_f_3222_: *mut crate::leanh::LeanObject,
    mut v_x_3223_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_3223_) == 0 {
        let mut v_toApplicative_3224_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_toPure_3225_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3226_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3227_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_toApplicative_3224_ = crate::leanh::lean_ctor_get(v_inst_3221_, 0);
        crate::leanh::lean_inc_ref(v_toApplicative_3224_);
        crate::leanh::lean_dec(v_f_3222_);
        crate::leanh::lean_dec_ref(v_inst_3221_);
        v_toPure_3225_ = crate::leanh::lean_ctor_get(v_toApplicative_3224_, 1);
        crate::leanh::lean_inc(v_toPure_3225_);
        crate::leanh::lean_dec_ref(v_toApplicative_3224_);
        v___x_3226_ = crate::leanh::lean_box(0);
        v___x_3227_ =
            crate::leanh::lean_apply_2(v_toPure_3225_, crate::leanh::lean_box(0), v___x_3226_);
        return v___x_3227_;
    } else {
        let mut v_toBind_3228_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_lchild_3229_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_key_3230_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_val_3231_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_rchild_3232_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___f_3233_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___f_3234_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3235_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3236_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_toBind_3228_ = crate::leanh::lean_ctor_get(v_inst_3221_, 1);
        crate::leanh::lean_inc_n(v_toBind_3228_, 2);
        v_lchild_3229_ = crate::leanh::lean_ctor_get(v_x_3223_, 0);
        crate::leanh::lean_inc(v_lchild_3229_);
        v_key_3230_ = crate::leanh::lean_ctor_get(v_x_3223_, 1);
        crate::leanh::lean_inc(v_key_3230_);
        v_val_3231_ = crate::leanh::lean_ctor_get(v_x_3223_, 2);
        crate::leanh::lean_inc(v_val_3231_);
        v_rchild_3232_ = crate::leanh::lean_ctor_get(v_x_3223_, 3);
        crate::leanh::lean_inc(v_rchild_3232_);
        crate::leanh::lean_dec_ref_known(v_x_3223_, 4);
        crate::leanh::lean_inc_n(v_f_3222_, 2);
        crate::leanh::lean_inc_ref(v_inst_3221_);
        v___f_3233_ = crate::leanh::lean_alloc_closure(
            l_Lean_RBNode_forM___redArg___lam__0 as *mut core::ffi::c_void,
            4,
            3,
        );
        crate::leanh::lean_closure_set(v___f_3233_, 0, v_inst_3221_);
        crate::leanh::lean_closure_set(v___f_3233_, 1, v_f_3222_);
        crate::leanh::lean_closure_set(v___f_3233_, 2, v_rchild_3232_);
        v___f_3234_ = crate::leanh::lean_alloc_closure(
            l_Lean_RBNode_forM___redArg___lam__1 as *mut core::ffi::c_void,
            6,
            5,
        );
        crate::leanh::lean_closure_set(v___f_3234_, 0, v_f_3222_);
        crate::leanh::lean_closure_set(v___f_3234_, 1, v_key_3230_);
        crate::leanh::lean_closure_set(v___f_3234_, 2, v_val_3231_);
        crate::leanh::lean_closure_set(v___f_3234_, 3, v_toBind_3228_);
        crate::leanh::lean_closure_set(v___f_3234_, 4, v___f_3233_);
        v___x_3235_ = l_Lean_RBNode_forM___redArg(v_inst_3221_, v_f_3222_, v_lchild_3229_);
        v___x_3236_ = crate::leanh::lean_apply_4(
            v_toBind_3228_,
            crate::leanh::lean_box(0),
            crate::leanh::lean_box(0),
            v___x_3235_,
            v___f_3234_,
        );
        return v___x_3236_;
    }
}
pub unsafe fn l_Lean_RBNode_forM___redArg___lam__0(
    mut v_inst_3237_: *mut crate::leanh::LeanObject,
    mut v_f_3238_: *mut crate::leanh::LeanObject,
    mut v_rchild_3239_: *mut crate::leanh::LeanObject,
    mut v_____r_3240_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3241_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3241_ = l_Lean_RBNode_forM___redArg(v_inst_3237_, v_f_3238_, v_rchild_3239_);
    return v___x_3241_;
}
pub unsafe fn l_Lean_RBNode_forM(
    mut v_00_u03b1_3242_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_3243_: *mut crate::leanh::LeanObject,
    mut v_m_3244_: *mut crate::leanh::LeanObject,
    mut v_inst_3245_: *mut crate::leanh::LeanObject,
    mut v_f_3246_: *mut crate::leanh::LeanObject,
    mut v_x_3247_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3248_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3248_ = l_Lean_RBNode_forM___redArg(v_inst_3245_, v_f_3246_, v_x_3247_);
    return v___x_3248_;
}
pub unsafe fn l_Lean_RBNode_foldM___redArg___lam__1(
    mut v_f_3249_: *mut crate::leanh::LeanObject,
    mut v_key_3250_: *mut crate::leanh::LeanObject,
    mut v_val_3251_: *mut crate::leanh::LeanObject,
    mut v_toBind_3252_: *mut crate::leanh::LeanObject,
    mut v___f_3253_: *mut crate::leanh::LeanObject,
    mut v_b_3254_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3255_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3256_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3255_ = crate::leanh::lean_apply_3(v_f_3249_, v_b_3254_, v_key_3250_, v_val_3251_);
    v___x_3256_ = crate::leanh::lean_apply_4(
        v_toBind_3252_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___x_3255_,
        v___f_3253_,
    );
    return v___x_3256_;
}
pub unsafe fn l_Lean_RBNode_foldM___redArg(
    mut v_inst_3257_: *mut crate::leanh::LeanObject,
    mut v_f_3258_: *mut crate::leanh::LeanObject,
    mut v_x_3259_: *mut crate::leanh::LeanObject,
    mut v_x_3260_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_3260_) == 0 {
        let mut v_toApplicative_3261_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_toPure_3262_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3263_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_toApplicative_3261_ = crate::leanh::lean_ctor_get(v_inst_3257_, 0);
        crate::leanh::lean_inc_ref(v_toApplicative_3261_);
        crate::leanh::lean_dec(v_f_3258_);
        crate::leanh::lean_dec_ref(v_inst_3257_);
        v_toPure_3262_ = crate::leanh::lean_ctor_get(v_toApplicative_3261_, 1);
        crate::leanh::lean_inc(v_toPure_3262_);
        crate::leanh::lean_dec_ref(v_toApplicative_3261_);
        v___x_3263_ =
            crate::leanh::lean_apply_2(v_toPure_3262_, crate::leanh::lean_box(0), v_x_3259_);
        return v___x_3263_;
    } else {
        let mut v_toBind_3264_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_lchild_3265_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_key_3266_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_val_3267_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_rchild_3268_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___f_3269_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___f_3270_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3271_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3272_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_toBind_3264_ = crate::leanh::lean_ctor_get(v_inst_3257_, 1);
        crate::leanh::lean_inc_n(v_toBind_3264_, 2);
        v_lchild_3265_ = crate::leanh::lean_ctor_get(v_x_3260_, 0);
        crate::leanh::lean_inc(v_lchild_3265_);
        v_key_3266_ = crate::leanh::lean_ctor_get(v_x_3260_, 1);
        crate::leanh::lean_inc(v_key_3266_);
        v_val_3267_ = crate::leanh::lean_ctor_get(v_x_3260_, 2);
        crate::leanh::lean_inc(v_val_3267_);
        v_rchild_3268_ = crate::leanh::lean_ctor_get(v_x_3260_, 3);
        crate::leanh::lean_inc(v_rchild_3268_);
        crate::leanh::lean_dec_ref_known(v_x_3260_, 4);
        crate::leanh::lean_inc_n(v_f_3258_, 2);
        crate::leanh::lean_inc_ref(v_inst_3257_);
        v___f_3269_ = crate::leanh::lean_alloc_closure(
            l_Lean_RBNode_foldM___redArg___lam__0 as *mut core::ffi::c_void,
            4,
            3,
        );
        crate::leanh::lean_closure_set(v___f_3269_, 0, v_inst_3257_);
        crate::leanh::lean_closure_set(v___f_3269_, 1, v_f_3258_);
        crate::leanh::lean_closure_set(v___f_3269_, 2, v_rchild_3268_);
        v___f_3270_ = crate::leanh::lean_alloc_closure(
            l_Lean_RBNode_foldM___redArg___lam__1 as *mut core::ffi::c_void,
            6,
            5,
        );
        crate::leanh::lean_closure_set(v___f_3270_, 0, v_f_3258_);
        crate::leanh::lean_closure_set(v___f_3270_, 1, v_key_3266_);
        crate::leanh::lean_closure_set(v___f_3270_, 2, v_val_3267_);
        crate::leanh::lean_closure_set(v___f_3270_, 3, v_toBind_3264_);
        crate::leanh::lean_closure_set(v___f_3270_, 4, v___f_3269_);
        v___x_3271_ =
            l_Lean_RBNode_foldM___redArg(v_inst_3257_, v_f_3258_, v_x_3259_, v_lchild_3265_);
        v___x_3272_ = crate::leanh::lean_apply_4(
            v_toBind_3264_,
            crate::leanh::lean_box(0),
            crate::leanh::lean_box(0),
            v___x_3271_,
            v___f_3270_,
        );
        return v___x_3272_;
    }
}
pub unsafe fn l_Lean_RBNode_foldM___redArg___lam__0(
    mut v_inst_3273_: *mut crate::leanh::LeanObject,
    mut v_f_3274_: *mut crate::leanh::LeanObject,
    mut v_rchild_3275_: *mut crate::leanh::LeanObject,
    mut v_b_3276_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3277_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3277_ = l_Lean_RBNode_foldM___redArg(v_inst_3273_, v_f_3274_, v_b_3276_, v_rchild_3275_);
    return v___x_3277_;
}
pub unsafe fn l_Lean_RBNode_foldM(
    mut v_00_u03b1_3278_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_3279_: *mut crate::leanh::LeanObject,
    mut v_00_u03c3_3280_: *mut crate::leanh::LeanObject,
    mut v_m_3281_: *mut crate::leanh::LeanObject,
    mut v_inst_3282_: *mut crate::leanh::LeanObject,
    mut v_f_3283_: *mut crate::leanh::LeanObject,
    mut v_x_3284_: *mut crate::leanh::LeanObject,
    mut v_x_3285_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3286_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3286_ = l_Lean_RBNode_foldM___redArg(v_inst_3282_, v_f_3283_, v_x_3284_, v_x_3285_);
    return v___x_3286_;
}
pub unsafe fn l___private_Lean_Data_RBMap_0__Lean_RBNode_forIn_visit___redArg___lam__1(
    mut v_toPure_3287_: *mut crate::leanh::LeanObject,
    mut v_f_3288_: *mut crate::leanh::LeanObject,
    mut v_key_3289_: *mut crate::leanh::LeanObject,
    mut v_val_3290_: *mut crate::leanh::LeanObject,
    mut v_toBind_3291_: *mut crate::leanh::LeanObject,
    mut v___f_3292_: *mut crate::leanh::LeanObject,
    mut v_____do__lift_3293_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_____do__lift_3293_) == 0 {
        let mut v___x_3294_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v___f_3292_);
        crate::leanh::lean_dec(v_toBind_3291_);
        crate::leanh::lean_dec(v_val_3290_);
        crate::leanh::lean_dec(v_key_3289_);
        crate::leanh::lean_dec(v_f_3288_);
        v___x_3294_ = crate::leanh::lean_apply_2(
            v_toPure_3287_,
            crate::leanh::lean_box(0),
            v_____do__lift_3293_,
        );
        return v___x_3294_;
    } else {
        let mut v_a_3295_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3296_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3297_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_toPure_3287_);
        v_a_3295_ = crate::leanh::lean_ctor_get(v_____do__lift_3293_, 0);
        crate::leanh::lean_inc(v_a_3295_);
        crate::leanh::lean_dec_ref_known(v_____do__lift_3293_, 1);
        v___x_3296_ = crate::leanh::lean_apply_3(v_f_3288_, v_key_3289_, v_val_3290_, v_a_3295_);
        v___x_3297_ = crate::leanh::lean_apply_4(
            v_toBind_3291_,
            crate::leanh::lean_box(0),
            crate::leanh::lean_box(0),
            v___x_3296_,
            v___f_3292_,
        );
        return v___x_3297_;
    }
}
pub unsafe fn l___private_Lean_Data_RBMap_0__Lean_RBNode_forIn_visit___redArg(
    mut v_inst_3298_: *mut crate::leanh::LeanObject,
    mut v_f_3299_: *mut crate::leanh::LeanObject,
    mut v_a_3300_: *mut crate::leanh::LeanObject,
    mut v_a_3301_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_a_3300_) == 0 {
        let mut v_toApplicative_3302_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_toPure_3303_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3304_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3305_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_toApplicative_3302_ = crate::leanh::lean_ctor_get(v_inst_3298_, 0);
        crate::leanh::lean_inc_ref(v_toApplicative_3302_);
        crate::leanh::lean_dec(v_f_3299_);
        crate::leanh::lean_dec_ref(v_inst_3298_);
        v_toPure_3303_ = crate::leanh::lean_ctor_get(v_toApplicative_3302_, 1);
        crate::leanh::lean_inc(v_toPure_3303_);
        crate::leanh::lean_dec_ref(v_toApplicative_3302_);
        v___x_3304_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_3304_, 0, v_a_3301_);
        v___x_3305_ =
            crate::leanh::lean_apply_2(v_toPure_3303_, crate::leanh::lean_box(0), v___x_3304_);
        return v___x_3305_;
    } else {
        let mut v_toApplicative_3306_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_toBind_3307_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_toPure_3308_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_lchild_3309_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_key_3310_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_val_3311_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_rchild_3312_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___f_3313_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___f_3314_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3315_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3316_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_toApplicative_3306_ = crate::leanh::lean_ctor_get(v_inst_3298_, 0);
        v_toBind_3307_ = crate::leanh::lean_ctor_get(v_inst_3298_, 1);
        crate::leanh::lean_inc_n(v_toBind_3307_, 2);
        v_toPure_3308_ = crate::leanh::lean_ctor_get(v_toApplicative_3306_, 1);
        v_lchild_3309_ = crate::leanh::lean_ctor_get(v_a_3300_, 0);
        crate::leanh::lean_inc(v_lchild_3309_);
        v_key_3310_ = crate::leanh::lean_ctor_get(v_a_3300_, 1);
        crate::leanh::lean_inc(v_key_3310_);
        v_val_3311_ = crate::leanh::lean_ctor_get(v_a_3300_, 2);
        crate::leanh::lean_inc(v_val_3311_);
        v_rchild_3312_ = crate::leanh::lean_ctor_get(v_a_3300_, 3);
        crate::leanh::lean_inc(v_rchild_3312_);
        crate::leanh::lean_dec_ref_known(v_a_3300_, 4);
        crate::leanh::lean_inc_n(v_f_3299_, 2);
        crate::leanh::lean_inc_ref(v_inst_3298_);
        crate::leanh::lean_inc_n(v_toPure_3308_, 2);
        v___f_3313_ = crate::leanh::lean_alloc_closure(
            l___private_Lean_Data_RBMap_0__Lean_RBNode_forIn_visit___redArg___lam__0
                as *mut core::ffi::c_void,
            5,
            4,
        );
        crate::leanh::lean_closure_set(v___f_3313_, 0, v_toPure_3308_);
        crate::leanh::lean_closure_set(v___f_3313_, 1, v_inst_3298_);
        crate::leanh::lean_closure_set(v___f_3313_, 2, v_f_3299_);
        crate::leanh::lean_closure_set(v___f_3313_, 3, v_rchild_3312_);
        v___f_3314_ = crate::leanh::lean_alloc_closure(
            l___private_Lean_Data_RBMap_0__Lean_RBNode_forIn_visit___redArg___lam__1
                as *mut core::ffi::c_void,
            7,
            6,
        );
        crate::leanh::lean_closure_set(v___f_3314_, 0, v_toPure_3308_);
        crate::leanh::lean_closure_set(v___f_3314_, 1, v_f_3299_);
        crate::leanh::lean_closure_set(v___f_3314_, 2, v_key_3310_);
        crate::leanh::lean_closure_set(v___f_3314_, 3, v_val_3311_);
        crate::leanh::lean_closure_set(v___f_3314_, 4, v_toBind_3307_);
        crate::leanh::lean_closure_set(v___f_3314_, 5, v___f_3313_);
        v___x_3315_ = l___private_Lean_Data_RBMap_0__Lean_RBNode_forIn_visit___redArg(
            v_inst_3298_,
            v_f_3299_,
            v_lchild_3309_,
            v_a_3301_,
        );
        v___x_3316_ = crate::leanh::lean_apply_4(
            v_toBind_3307_,
            crate::leanh::lean_box(0),
            crate::leanh::lean_box(0),
            v___x_3315_,
            v___f_3314_,
        );
        return v___x_3316_;
    }
}
pub unsafe fn l___private_Lean_Data_RBMap_0__Lean_RBNode_forIn_visit___redArg___lam__0(
    mut v_toPure_3317_: *mut crate::leanh::LeanObject,
    mut v_inst_3318_: *mut crate::leanh::LeanObject,
    mut v_f_3319_: *mut crate::leanh::LeanObject,
    mut v_rchild_3320_: *mut crate::leanh::LeanObject,
    mut v_____do__lift_3321_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_____do__lift_3321_) == 0 {
        let mut v___x_3322_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_rchild_3320_);
        crate::leanh::lean_dec(v_f_3319_);
        crate::leanh::lean_dec_ref(v_inst_3318_);
        v___x_3322_ = crate::leanh::lean_apply_2(
            v_toPure_3317_,
            crate::leanh::lean_box(0),
            v_____do__lift_3321_,
        );
        return v___x_3322_;
    } else {
        let mut v_a_3323_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3324_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_toPure_3317_);
        v_a_3323_ = crate::leanh::lean_ctor_get(v_____do__lift_3321_, 0);
        crate::leanh::lean_inc(v_a_3323_);
        crate::leanh::lean_dec_ref_known(v_____do__lift_3321_, 1);
        v___x_3324_ = l___private_Lean_Data_RBMap_0__Lean_RBNode_forIn_visit___redArg(
            v_inst_3318_,
            v_f_3319_,
            v_rchild_3320_,
            v_a_3323_,
        );
        return v___x_3324_;
    }
}
pub unsafe fn l___private_Lean_Data_RBMap_0__Lean_RBNode_forIn_visit(
    mut v_00_u03b1_3325_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_3326_: *mut crate::leanh::LeanObject,
    mut v_00_u03c3_3327_: *mut crate::leanh::LeanObject,
    mut v_m_3328_: *mut crate::leanh::LeanObject,
    mut v_inst_3329_: *mut crate::leanh::LeanObject,
    mut v_f_3330_: *mut crate::leanh::LeanObject,
    mut v_a_3331_: *mut crate::leanh::LeanObject,
    mut v_a_3332_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3333_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3333_ = l___private_Lean_Data_RBMap_0__Lean_RBNode_forIn_visit___redArg(
        v_inst_3329_,
        v_f_3330_,
        v_a_3331_,
        v_a_3332_,
    );
    return v___x_3333_;
}
pub unsafe fn l_Lean_RBNode_forIn___redArg___lam__0(
    mut v_toPure_3334_: *mut crate::leanh::LeanObject,
    mut v_____do__lift_3335_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_a_3336_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3337_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_a_3336_ = crate::leanh::lean_ctor_get(v_____do__lift_3335_, 0);
    crate::leanh::lean_inc(v_a_3336_);
    crate::leanh::lean_dec_ref(v_____do__lift_3335_);
    v___x_3337_ = crate::leanh::lean_apply_2(v_toPure_3334_, crate::leanh::lean_box(0), v_a_3336_);
    return v___x_3337_;
}
pub unsafe fn l_Lean_RBNode_forIn___redArg(
    mut v_inst_3338_: *mut crate::leanh::LeanObject,
    mut v_as_3339_: *mut crate::leanh::LeanObject,
    mut v_init_3340_: *mut crate::leanh::LeanObject,
    mut v_f_3341_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toApplicative_3342_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_3343_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_3344_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3345_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3346_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3347_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_3342_ = crate::leanh::lean_ctor_get(v_inst_3338_, 0);
    v_toBind_3343_ = crate::leanh::lean_ctor_get(v_inst_3338_, 1);
    crate::leanh::lean_inc(v_toBind_3343_);
    v_toPure_3344_ = crate::leanh::lean_ctor_get(v_toApplicative_3342_, 1);
    crate::leanh::lean_inc(v_toPure_3344_);
    v___x_3345_ = l___private_Lean_Data_RBMap_0__Lean_RBNode_forIn_visit___redArg(
        v_inst_3338_,
        v_f_3341_,
        v_as_3339_,
        v_init_3340_,
    );
    v___f_3346_ = crate::leanh::lean_alloc_closure(
        l_Lean_RBNode_forIn___redArg___lam__0 as *mut core::ffi::c_void,
        2,
        1,
    );
    crate::leanh::lean_closure_set(v___f_3346_, 0, v_toPure_3344_);
    v___x_3347_ = crate::leanh::lean_apply_4(
        v_toBind_3343_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___x_3345_,
        v___f_3346_,
    );
    return v___x_3347_;
}
pub unsafe fn l_Lean_RBNode_forIn(
    mut v_00_u03b1_3348_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_3349_: *mut crate::leanh::LeanObject,
    mut v_00_u03c3_3350_: *mut crate::leanh::LeanObject,
    mut v_m_3351_: *mut crate::leanh::LeanObject,
    mut v_inst_3352_: *mut crate::leanh::LeanObject,
    mut v_as_3353_: *mut crate::leanh::LeanObject,
    mut v_init_3354_: *mut crate::leanh::LeanObject,
    mut v_f_3355_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toApplicative_3356_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_3357_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_3358_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3359_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3360_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3361_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_3356_ = crate::leanh::lean_ctor_get(v_inst_3352_, 0);
    v_toBind_3357_ = crate::leanh::lean_ctor_get(v_inst_3352_, 1);
    crate::leanh::lean_inc(v_toBind_3357_);
    v_toPure_3358_ = crate::leanh::lean_ctor_get(v_toApplicative_3356_, 1);
    crate::leanh::lean_inc(v_toPure_3358_);
    v___x_3359_ = l___private_Lean_Data_RBMap_0__Lean_RBNode_forIn_visit___redArg(
        v_inst_3352_,
        v_f_3355_,
        v_as_3353_,
        v_init_3354_,
    );
    v___f_3360_ = crate::leanh::lean_alloc_closure(
        l_Lean_RBNode_forIn___redArg___lam__0 as *mut core::ffi::c_void,
        2,
        1,
    );
    crate::leanh::lean_closure_set(v___f_3360_, 0, v_toPure_3358_);
    v___x_3361_ = crate::leanh::lean_apply_4(
        v_toBind_3357_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___x_3359_,
        v___f_3360_,
    );
    return v___x_3361_;
}
pub unsafe fn l_Lean_RBNode_revFold___redArg(
    mut v_f_3362_: *mut crate::leanh::LeanObject,
    mut v_x_3363_: *mut crate::leanh::LeanObject,
    mut v_x_3364_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_lchild_3365_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_key_3366_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_3367_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_rchild_3368_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3369_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3370_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_3364_) == 0 {
                    crate::leanh::lean_dec(v_f_3362_);
                    return v_x_3363_;
                } else {
                    v_lchild_3365_ = crate::leanh::lean_ctor_get(v_x_3364_, 0);
                    crate::leanh::lean_inc(v_lchild_3365_);
                    v_key_3366_ = crate::leanh::lean_ctor_get(v_x_3364_, 1);
                    crate::leanh::lean_inc(v_key_3366_);
                    v_val_3367_ = crate::leanh::lean_ctor_get(v_x_3364_, 2);
                    crate::leanh::lean_inc(v_val_3367_);
                    v_rchild_3368_ = crate::leanh::lean_ctor_get(v_x_3364_, 3);
                    crate::leanh::lean_inc(v_rchild_3368_);
                    crate::leanh::lean_dec_ref_known(v_x_3364_, 4);
                    crate::leanh::lean_inc_n(v_f_3362_, 2);
                    v___x_3369_ =
                        l_Lean_RBNode_revFold___redArg(v_f_3362_, v_x_3363_, v_rchild_3368_);
                    v___x_3370_ = crate::leanh::lean_apply_3(
                        v_f_3362_,
                        v___x_3369_,
                        v_key_3366_,
                        v_val_3367_,
                    );
                    v_x_3363_ = v___x_3370_;
                    v_x_3364_ = v_lchild_3365_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_RBNode_revFold(
    mut v_00_u03b1_3372_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_3373_: *mut crate::leanh::LeanObject,
    mut v_00_u03c3_3374_: *mut crate::leanh::LeanObject,
    mut v_f_3375_: *mut crate::leanh::LeanObject,
    mut v_x_3376_: *mut crate::leanh::LeanObject,
    mut v_x_3377_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3378_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3378_ = l_Lean_RBNode_revFold___redArg(v_f_3375_, v_x_3376_, v_x_3377_);
    return v___x_3378_;
}
pub unsafe fn l_Lean_RBNode_all___redArg(
    mut v_p_3379_: *mut crate::leanh::LeanObject,
    mut v_x_3380_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_3381_: u8 = 0;
    let mut v_lchild_3382_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_key_3383_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_3384_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_rchild_3385_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3386_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3387_: u8 = 0;
    let mut v___x_3388_: u8 = 0;
    let mut v___x_3389_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_3380_) == 0 {
                    crate::leanh::lean_dec_ref(v_p_3379_);
                    v___x_3381_ = 1;
                    return v___x_3381_;
                } else {
                    v_lchild_3382_ = crate::leanh::lean_ctor_get(v_x_3380_, 0);
                    crate::leanh::lean_inc(v_lchild_3382_);
                    v_key_3383_ = crate::leanh::lean_ctor_get(v_x_3380_, 1);
                    crate::leanh::lean_inc(v_key_3383_);
                    v_val_3384_ = crate::leanh::lean_ctor_get(v_x_3380_, 2);
                    crate::leanh::lean_inc(v_val_3384_);
                    v_rchild_3385_ = crate::leanh::lean_ctor_get(v_x_3380_, 3);
                    crate::leanh::lean_inc(v_rchild_3385_);
                    crate::leanh::lean_dec_ref_known(v_x_3380_, 4);
                    crate::leanh::lean_inc_ref(v_p_3379_);
                    v___x_3386_ = crate::leanh::lean_apply_2(v_p_3379_, v_key_3383_, v_val_3384_);
                    v___x_3387_ = (crate::leanh::lean_unbox(v___x_3386_) as u8);
                    if v___x_3387_ == 0 {
                        crate::leanh::lean_dec(v_rchild_3385_);
                        crate::leanh::lean_dec(v_lchild_3382_);
                        crate::leanh::lean_dec_ref(v_p_3379_);
                        v___x_3388_ = (crate::leanh::lean_unbox(v___x_3386_) as u8);
                        return v___x_3388_;
                    } else {
                        crate::leanh::lean_inc_ref(v_p_3379_);
                        v___x_3389_ = l_Lean_RBNode_all___redArg(v_p_3379_, v_lchild_3382_);
                        if v___x_3389_ == 0 {
                            crate::leanh::lean_dec(v_rchild_3385_);
                            crate::leanh::lean_dec_ref(v_p_3379_);
                            return v___x_3389_;
                        } else {
                            v_x_3380_ = v_rchild_3385_;
                            state = 0;
                            continue;
                        }
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_RBNode_all___redArg___boxed(
    mut v_p_3391_: *mut crate::leanh::LeanObject,
    mut v_x_3392_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3393_: u8 = 0;
    let mut v_r_3394_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3393_ = l_Lean_RBNode_all___redArg(v_p_3391_, v_x_3392_);
    v_r_3394_ = crate::leanh::lean_box((v_res_3393_) as usize);
    return v_r_3394_;
}
pub unsafe fn l_Lean_RBNode_all(
    mut v_00_u03b1_3395_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_3396_: *mut crate::leanh::LeanObject,
    mut v_p_3397_: *mut crate::leanh::LeanObject,
    mut v_x_3398_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_3399_: u8 = 0;
    v___x_3399_ = l_Lean_RBNode_all___redArg(v_p_3397_, v_x_3398_);
    return v___x_3399_;
}
pub unsafe fn l_Lean_RBNode_all___boxed(
    mut v_00_u03b1_3400_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_3401_: *mut crate::leanh::LeanObject,
    mut v_p_3402_: *mut crate::leanh::LeanObject,
    mut v_x_3403_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3404_: u8 = 0;
    let mut v_r_3405_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3404_ = l_Lean_RBNode_all(v_00_u03b1_3400_, v_00_u03b2_3401_, v_p_3402_, v_x_3403_);
    v_r_3405_ = crate::leanh::lean_box((v_res_3404_) as usize);
    return v_r_3405_;
}
pub unsafe fn l_Lean_RBNode_any___redArg(
    mut v_p_3406_: *mut crate::leanh::LeanObject,
    mut v_x_3407_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_3408_: u8 = 0;
    let mut v_lchild_3409_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_key_3410_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_3411_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_rchild_3412_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3413_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3414_: u8 = 0;
    let mut v___x_3415_: u8 = 0;
    let mut v___x_3417_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_3407_) == 0 {
                    crate::leanh::lean_dec_ref(v_p_3406_);
                    v___x_3408_ = 0;
                    return v___x_3408_;
                } else {
                    v_lchild_3409_ = crate::leanh::lean_ctor_get(v_x_3407_, 0);
                    crate::leanh::lean_inc(v_lchild_3409_);
                    v_key_3410_ = crate::leanh::lean_ctor_get(v_x_3407_, 1);
                    crate::leanh::lean_inc(v_key_3410_);
                    v_val_3411_ = crate::leanh::lean_ctor_get(v_x_3407_, 2);
                    crate::leanh::lean_inc(v_val_3411_);
                    v_rchild_3412_ = crate::leanh::lean_ctor_get(v_x_3407_, 3);
                    crate::leanh::lean_inc(v_rchild_3412_);
                    crate::leanh::lean_dec_ref_known(v_x_3407_, 4);
                    crate::leanh::lean_inc_ref(v_p_3406_);
                    v___x_3413_ = crate::leanh::lean_apply_2(v_p_3406_, v_key_3410_, v_val_3411_);
                    v___x_3414_ = (crate::leanh::lean_unbox(v___x_3413_) as u8);
                    if v___x_3414_ == 0 {
                        crate::leanh::lean_inc_ref(v_p_3406_);
                        v___x_3415_ = l_Lean_RBNode_any___redArg(v_p_3406_, v_lchild_3409_);
                        if v___x_3415_ == 0 {
                            v_x_3407_ = v_rchild_3412_;
                            state = 0;
                            continue;
                        } else {
                            crate::leanh::lean_dec(v_rchild_3412_);
                            crate::leanh::lean_dec_ref(v_p_3406_);
                            return v___x_3415_;
                        }
                    } else {
                        crate::leanh::lean_dec(v_rchild_3412_);
                        crate::leanh::lean_dec(v_lchild_3409_);
                        crate::leanh::lean_dec_ref(v_p_3406_);
                        v___x_3417_ = (crate::leanh::lean_unbox(v___x_3413_) as u8);
                        return v___x_3417_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_RBNode_any___redArg___boxed(
    mut v_p_3418_: *mut crate::leanh::LeanObject,
    mut v_x_3419_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3420_: u8 = 0;
    let mut v_r_3421_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3420_ = l_Lean_RBNode_any___redArg(v_p_3418_, v_x_3419_);
    v_r_3421_ = crate::leanh::lean_box((v_res_3420_) as usize);
    return v_r_3421_;
}
pub unsafe fn l_Lean_RBNode_any(
    mut v_00_u03b1_3422_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_3423_: *mut crate::leanh::LeanObject,
    mut v_p_3424_: *mut crate::leanh::LeanObject,
    mut v_x_3425_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_3426_: u8 = 0;
    v___x_3426_ = l_Lean_RBNode_any___redArg(v_p_3424_, v_x_3425_);
    return v___x_3426_;
}
pub unsafe fn l_Lean_RBNode_any___boxed(
    mut v_00_u03b1_3427_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_3428_: *mut crate::leanh::LeanObject,
    mut v_p_3429_: *mut crate::leanh::LeanObject,
    mut v_x_3430_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3431_: u8 = 0;
    let mut v_r_3432_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3431_ = l_Lean_RBNode_any(v_00_u03b1_3427_, v_00_u03b2_3428_, v_p_3429_, v_x_3430_);
    v_r_3432_ = crate::leanh::lean_box((v_res_3431_) as usize);
    return v_r_3432_;
}
pub unsafe fn l_Lean_RBNode_singleton___redArg(
    mut v_k_3433_: *mut crate::leanh::LeanObject,
    mut v_v_3434_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3435_: u8 = 0;
    let mut v___x_3436_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3437_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3435_ = 0;
    v___x_3436_ = crate::leanh::lean_box(0);
    v___x_3437_ = crate::leanh::lean_alloc_ctor(1, 4, (1) as u32);
    crate::leanh::lean_ctor_set(v___x_3437_, 0, v___x_3436_);
    crate::leanh::lean_ctor_set(v___x_3437_, 1, v_k_3433_);
    crate::leanh::lean_ctor_set(v___x_3437_, 2, v_v_3434_);
    crate::leanh::lean_ctor_set(v___x_3437_, 3, v___x_3436_);
    crate::leanh::lean_ctor_set_uint8(
        v___x_3437_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 4) as u32,
        v___x_3435_,
    );
    return v___x_3437_;
}
pub unsafe fn l_Lean_RBNode_singleton(
    mut v_00_u03b1_3438_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_3439_: *mut crate::leanh::LeanObject,
    mut v_k_3440_: *mut crate::leanh::LeanObject,
    mut v_v_3441_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3442_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3442_ = l_Lean_RBNode_singleton___redArg(v_k_3440_, v_v_3441_);
    return v___x_3442_;
}
pub unsafe fn l_Lean_RBNode_isSingleton___redArg(
    mut v_x_3443_: *mut crate::leanh::LeanObject,
) -> u8 {
    if crate::leanh::lean_obj_tag(v_x_3443_) == 1 {
        let mut v_lchild_3444_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_lchild_3444_ = crate::leanh::lean_ctor_get(v_x_3443_, 0);
        if crate::leanh::lean_obj_tag(v_lchild_3444_) == 0 {
            let mut v_rchild_3445_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v_rchild_3445_ = crate::leanh::lean_ctor_get(v_x_3443_, 3);
            if crate::leanh::lean_obj_tag(v_rchild_3445_) == 0 {
                let mut v___x_3446_: u8 = 0;
                v___x_3446_ = 1;
                return v___x_3446_;
            } else {
                let mut v___x_3447_: u8 = 0;
                v___x_3447_ = 0;
                return v___x_3447_;
            }
        } else {
            let mut v___x_3448_: u8 = 0;
            v___x_3448_ = 0;
            return v___x_3448_;
        }
    } else {
        let mut v___x_3449_: u8 = 0;
        v___x_3449_ = 0;
        return v___x_3449_;
    }
}
pub unsafe fn l_Lean_RBNode_isSingleton___redArg___boxed(
    mut v_x_3450_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3451_: u8 = 0;
    let mut v_r_3452_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3451_ = l_Lean_RBNode_isSingleton___redArg(v_x_3450_);
    crate::leanh::lean_dec(v_x_3450_);
    v_r_3452_ = crate::leanh::lean_box((v_res_3451_) as usize);
    return v_r_3452_;
}
pub unsafe fn l_Lean_RBNode_isSingleton(
    mut v_00_u03b1_3453_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_3454_: *mut crate::leanh::LeanObject,
    mut v_x_3455_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_3456_: u8 = 0;
    v___x_3456_ = l_Lean_RBNode_isSingleton___redArg(v_x_3455_);
    return v___x_3456_;
}
pub unsafe fn l_Lean_RBNode_isSingleton___boxed(
    mut v_00_u03b1_3457_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_3458_: *mut crate::leanh::LeanObject,
    mut v_x_3459_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3460_: u8 = 0;
    let mut v_r_3461_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3460_ = l_Lean_RBNode_isSingleton(v_00_u03b1_3457_, v_00_u03b2_3458_, v_x_3459_);
    crate::leanh::lean_dec(v_x_3459_);
    v_r_3461_ = crate::leanh::lean_box((v_res_3460_) as usize);
    return v_r_3461_;
}
pub unsafe fn l_Lean_RBNode_balance1___redArg(
    mut v_x_3462_: *mut crate::leanh::LeanObject,
    mut v_x_3463_: *mut crate::leanh::LeanObject,
    mut v_x_3464_: *mut crate::leanh::LeanObject,
    mut v_x_3465_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_a_3467_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_kx_3468_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_vx_3469_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_b_3470_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3471_: u8 = 0;
    let mut v___x_3472_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_color_3473_: u8 = 0;
    let mut v_lchild_3474_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_key_3475_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_3476_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_rchild_3477_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3479_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_kx_3480_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_vx_3481_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_b_3482_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ky_3483_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_vy_3484_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_c_3485_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_kz_3486_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_vz_3487_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_d_3488_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3489_: u8 = 0;
    let mut v___x_3490_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3491_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3492_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_color_3493_: u8 = 0;
    let mut v_lchild_3494_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_key_3495_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_3496_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_rchild_3497_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_color_3498_: u8 = 0;
    let mut v_lchild_3499_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_key_3500_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_3501_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_rchild_3502_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_color_3503_: u8 = 0;
    let mut v_lchild_3504_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_key_3505_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_3506_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_rchild_3507_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_3462_) == 1 {
                    v_color_3473_ = crate::leanh::lean_ctor_get_uint8(
                        v_x_3462_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 4) as u32,
                    );
                    v_lchild_3474_ = crate::leanh::lean_ctor_get(v_x_3462_, 0);
                    v_key_3475_ = crate::leanh::lean_ctor_get(v_x_3462_, 1);
                    v_val_3476_ = crate::leanh::lean_ctor_get(v_x_3462_, 2);
                    v_rchild_3477_ = crate::leanh::lean_ctor_get(v_x_3462_, 3);
                    if v_color_3473_ == 0 {
                        if crate::leanh::lean_obj_tag(v_lchild_3474_) == 1 {
                            v_color_3493_ = crate::leanh::lean_ctor_get_uint8(
                                v_lchild_3474_,
                                (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 4) as u32,
                            );
                            if v_color_3493_ == 0 {
                                crate::leanh::lean_inc_ref(v_lchild_3474_);
                                crate::leanh::lean_inc(v_rchild_3477_);
                                crate::leanh::lean_inc(v_val_3476_);
                                crate::leanh::lean_inc(v_key_3475_);
                                crate::leanh::lean_dec_ref_known(v_x_3462_, 4);
                                v_lchild_3494_ = crate::leanh::lean_ctor_get(v_lchild_3474_, 0);
                                crate::leanh::lean_inc(v_lchild_3494_);
                                v_key_3495_ = crate::leanh::lean_ctor_get(v_lchild_3474_, 1);
                                crate::leanh::lean_inc(v_key_3495_);
                                v_val_3496_ = crate::leanh::lean_ctor_get(v_lchild_3474_, 2);
                                crate::leanh::lean_inc(v_val_3496_);
                                v_rchild_3497_ = crate::leanh::lean_ctor_get(v_lchild_3474_, 3);
                                crate::leanh::lean_inc(v_rchild_3497_);
                                crate::leanh::lean_dec_ref_known(v_lchild_3474_, 4);
                                v_a_3479_ = v_lchild_3494_;
                                v_kx_3480_ = v_key_3495_;
                                v_vx_3481_ = v_val_3496_;
                                v_b_3482_ = v_rchild_3497_;
                                v_ky_3483_ = v_key_3475_;
                                v_vy_3484_ = v_val_3476_;
                                v_c_3485_ = v_rchild_3477_;
                                v_kz_3486_ = v_x_3463_;
                                v_vz_3487_ = v_x_3464_;
                                v_d_3488_ = v_x_3465_;
                                state = 2;
                                continue;
                            } else {
                                if crate::leanh::lean_obj_tag(v_rchild_3477_) == 1 {
                                    v_color_3498_ = crate::leanh::lean_ctor_get_uint8(
                                        v_rchild_3477_,
                                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 4)
                                            as u32,
                                    );
                                    if v_color_3498_ == 0 {
                                        crate::leanh::lean_inc_ref(v_rchild_3477_);
                                        crate::leanh::lean_inc_ref(v_lchild_3474_);
                                        crate::leanh::lean_inc(v_val_3476_);
                                        crate::leanh::lean_inc(v_key_3475_);
                                        crate::leanh::lean_dec_ref_known(v_x_3462_, 4);
                                        v_lchild_3499_ =
                                            crate::leanh::lean_ctor_get(v_rchild_3477_, 0);
                                        crate::leanh::lean_inc(v_lchild_3499_);
                                        v_key_3500_ =
                                            crate::leanh::lean_ctor_get(v_rchild_3477_, 1);
                                        crate::leanh::lean_inc(v_key_3500_);
                                        v_val_3501_ =
                                            crate::leanh::lean_ctor_get(v_rchild_3477_, 2);
                                        crate::leanh::lean_inc(v_val_3501_);
                                        v_rchild_3502_ =
                                            crate::leanh::lean_ctor_get(v_rchild_3477_, 3);
                                        crate::leanh::lean_inc(v_rchild_3502_);
                                        crate::leanh::lean_dec_ref_known(v_rchild_3477_, 4);
                                        v_a_3479_ = v_lchild_3474_;
                                        v_kx_3480_ = v_key_3475_;
                                        v_vx_3481_ = v_val_3476_;
                                        v_b_3482_ = v_lchild_3499_;
                                        v_ky_3483_ = v_key_3500_;
                                        v_vy_3484_ = v_val_3501_;
                                        v_c_3485_ = v_rchild_3502_;
                                        v_kz_3486_ = v_x_3463_;
                                        v_vz_3487_ = v_x_3464_;
                                        v_d_3488_ = v_x_3465_;
                                        state = 2;
                                        continue;
                                    } else {
                                        v_a_3467_ = v_x_3462_;
                                        v_kx_3468_ = v_x_3463_;
                                        v_vx_3469_ = v_x_3464_;
                                        v_b_3470_ = v_x_3465_;
                                        state = 1;
                                        continue;
                                    }
                                } else {
                                    v_a_3467_ = v_x_3462_;
                                    v_kx_3468_ = v_x_3463_;
                                    v_vx_3469_ = v_x_3464_;
                                    v_b_3470_ = v_x_3465_;
                                    state = 1;
                                    continue;
                                }
                            }
                        } else {
                            if crate::leanh::lean_obj_tag(v_rchild_3477_) == 1 {
                                v_color_3503_ = crate::leanh::lean_ctor_get_uint8(
                                    v_rchild_3477_,
                                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 4)
                                        as u32,
                                );
                                if v_color_3503_ == 0 {
                                    crate::leanh::lean_inc_ref(v_rchild_3477_);
                                    crate::leanh::lean_inc(v_val_3476_);
                                    crate::leanh::lean_inc(v_key_3475_);
                                    crate::leanh::lean_inc(v_lchild_3474_);
                                    crate::leanh::lean_dec_ref_known(v_x_3462_, 4);
                                    v_lchild_3504_ = crate::leanh::lean_ctor_get(v_rchild_3477_, 0);
                                    crate::leanh::lean_inc(v_lchild_3504_);
                                    v_key_3505_ = crate::leanh::lean_ctor_get(v_rchild_3477_, 1);
                                    crate::leanh::lean_inc(v_key_3505_);
                                    v_val_3506_ = crate::leanh::lean_ctor_get(v_rchild_3477_, 2);
                                    crate::leanh::lean_inc(v_val_3506_);
                                    v_rchild_3507_ = crate::leanh::lean_ctor_get(v_rchild_3477_, 3);
                                    crate::leanh::lean_inc(v_rchild_3507_);
                                    crate::leanh::lean_dec_ref_known(v_rchild_3477_, 4);
                                    v_a_3479_ = v_lchild_3474_;
                                    v_kx_3480_ = v_key_3475_;
                                    v_vx_3481_ = v_val_3476_;
                                    v_b_3482_ = v_lchild_3504_;
                                    v_ky_3483_ = v_key_3505_;
                                    v_vy_3484_ = v_val_3506_;
                                    v_c_3485_ = v_rchild_3507_;
                                    v_kz_3486_ = v_x_3463_;
                                    v_vz_3487_ = v_x_3464_;
                                    v_d_3488_ = v_x_3465_;
                                    state = 2;
                                    continue;
                                } else {
                                    v_a_3467_ = v_x_3462_;
                                    v_kx_3468_ = v_x_3463_;
                                    v_vx_3469_ = v_x_3464_;
                                    v_b_3470_ = v_x_3465_;
                                    state = 1;
                                    continue;
                                }
                            } else {
                                v_a_3467_ = v_x_3462_;
                                v_kx_3468_ = v_x_3463_;
                                v_vx_3469_ = v_x_3464_;
                                v_b_3470_ = v_x_3465_;
                                state = 1;
                                continue;
                            }
                        }
                    } else {
                        v_a_3467_ = v_x_3462_;
                        v_kx_3468_ = v_x_3463_;
                        v_vx_3469_ = v_x_3464_;
                        v_b_3470_ = v_x_3465_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_3467_ = v_x_3462_;
                    v_kx_3468_ = v_x_3463_;
                    v_vx_3469_ = v_x_3464_;
                    v_b_3470_ = v_x_3465_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_3471_ = 1;
                v___x_3472_ = crate::leanh::lean_alloc_ctor(1, 4, (1) as u32);
                crate::leanh::lean_ctor_set(v___x_3472_, 0, v_a_3467_);
                crate::leanh::lean_ctor_set(v___x_3472_, 1, v_kx_3468_);
                crate::leanh::lean_ctor_set(v___x_3472_, 2, v_vx_3469_);
                crate::leanh::lean_ctor_set(v___x_3472_, 3, v_b_3470_);
                crate::leanh::lean_ctor_set_uint8(
                    v___x_3472_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 4) as u32,
                    v___x_3471_,
                );
                return v___x_3472_;
            }
            2 => {
                v___x_3489_ = 1;
                v___x_3490_ = crate::leanh::lean_alloc_ctor(1, 4, (1) as u32);
                crate::leanh::lean_ctor_set(v___x_3490_, 0, v_a_3479_);
                crate::leanh::lean_ctor_set(v___x_3490_, 1, v_kx_3480_);
                crate::leanh::lean_ctor_set(v___x_3490_, 2, v_vx_3481_);
                crate::leanh::lean_ctor_set(v___x_3490_, 3, v_b_3482_);
                crate::leanh::lean_ctor_set_uint8(
                    v___x_3490_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 4) as u32,
                    v___x_3489_,
                );
                v___x_3491_ = crate::leanh::lean_alloc_ctor(1, 4, (1) as u32);
                crate::leanh::lean_ctor_set(v___x_3491_, 0, v_c_3485_);
                crate::leanh::lean_ctor_set(v___x_3491_, 1, v_kz_3486_);
                crate::leanh::lean_ctor_set(v___x_3491_, 2, v_vz_3487_);
                crate::leanh::lean_ctor_set(v___x_3491_, 3, v_d_3488_);
                crate::leanh::lean_ctor_set_uint8(
                    v___x_3491_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 4) as u32,
                    v___x_3489_,
                );
                v___x_3492_ = crate::leanh::lean_alloc_ctor(1, 4, (1) as u32);
                crate::leanh::lean_ctor_set(v___x_3492_, 0, v___x_3490_);
                crate::leanh::lean_ctor_set(v___x_3492_, 1, v_ky_3483_);
                crate::leanh::lean_ctor_set(v___x_3492_, 2, v_vy_3484_);
                crate::leanh::lean_ctor_set(v___x_3492_, 3, v___x_3491_);
                crate::leanh::lean_ctor_set_uint8(
                    v___x_3492_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 4) as u32,
                    v_color_3473_,
                );
                return v___x_3492_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_RBNode_balance1(
    mut v_00_u03b1_3508_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_3509_: *mut crate::leanh::LeanObject,
    mut v_x_3510_: *mut crate::leanh::LeanObject,
    mut v_x_3511_: *mut crate::leanh::LeanObject,
    mut v_x_3512_: *mut crate::leanh::LeanObject,
    mut v_x_3513_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_a_3515_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_kx_3516_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_vx_3517_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_b_3518_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3519_: u8 = 0;
    let mut v___x_3520_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_color_3521_: u8 = 0;
    let mut v_lchild_3522_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_key_3523_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_3524_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_rchild_3525_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3527_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_kx_3528_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_vx_3529_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_b_3530_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ky_3531_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_vy_3532_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_c_3533_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_kz_3534_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_vz_3535_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_d_3536_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3537_: u8 = 0;
    let mut v___x_3538_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3539_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3540_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_color_3541_: u8 = 0;
    let mut v_lchild_3542_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_key_3543_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_3544_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_rchild_3545_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_color_3546_: u8 = 0;
    let mut v_lchild_3547_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_key_3548_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_3549_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_rchild_3550_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_color_3551_: u8 = 0;
    let mut v_lchild_3552_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_key_3553_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_3554_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_rchild_3555_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_3510_) == 1 {
                    v_color_3521_ = crate::leanh::lean_ctor_get_uint8(
                        v_x_3510_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 4) as u32,
                    );
                    v_lchild_3522_ = crate::leanh::lean_ctor_get(v_x_3510_, 0);
                    v_key_3523_ = crate::leanh::lean_ctor_get(v_x_3510_, 1);
                    v_val_3524_ = crate::leanh::lean_ctor_get(v_x_3510_, 2);
                    v_rchild_3525_ = crate::leanh::lean_ctor_get(v_x_3510_, 3);
                    if v_color_3521_ == 0 {
                        if crate::leanh::lean_obj_tag(v_lchild_3522_) == 1 {
                            v_color_3541_ = crate::leanh::lean_ctor_get_uint8(
                                v_lchild_3522_,
                                (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 4) as u32,
                            );
                            if v_color_3541_ == 0 {
                                crate::leanh::lean_inc_ref(v_lchild_3522_);
                                crate::leanh::lean_inc(v_rchild_3525_);
                                crate::leanh::lean_inc(v_val_3524_);
                                crate::leanh::lean_inc(v_key_3523_);
                                crate::leanh::lean_dec_ref_known(v_x_3510_, 4);
                                v_lchild_3542_ = crate::leanh::lean_ctor_get(v_lchild_3522_, 0);
                                crate::leanh::lean_inc(v_lchild_3542_);
                                v_key_3543_ = crate::leanh::lean_ctor_get(v_lchild_3522_, 1);
                                crate::leanh::lean_inc(v_key_3543_);
                                v_val_3544_ = crate::leanh::lean_ctor_get(v_lchild_3522_, 2);
                                crate::leanh::lean_inc(v_val_3544_);
                                v_rchild_3545_ = crate::leanh::lean_ctor_get(v_lchild_3522_, 3);
                                crate::leanh::lean_inc(v_rchild_3545_);
                                crate::leanh::lean_dec_ref_known(v_lchild_3522_, 4);
                                v_a_3527_ = v_lchild_3542_;
                                v_kx_3528_ = v_key_3543_;
                                v_vx_3529_ = v_val_3544_;
                                v_b_3530_ = v_rchild_3545_;
                                v_ky_3531_ = v_key_3523_;
                                v_vy_3532_ = v_val_3524_;
                                v_c_3533_ = v_rchild_3525_;
                                v_kz_3534_ = v_x_3511_;
                                v_vz_3535_ = v_x_3512_;
                                v_d_3536_ = v_x_3513_;
                                state = 2;
                                continue;
                            } else {
                                if crate::leanh::lean_obj_tag(v_rchild_3525_) == 1 {
                                    v_color_3546_ = crate::leanh::lean_ctor_get_uint8(
                                        v_rchild_3525_,
                                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 4)
                                            as u32,
                                    );
                                    if v_color_3546_ == 0 {
                                        crate::leanh::lean_inc_ref(v_rchild_3525_);
                                        crate::leanh::lean_inc_ref(v_lchild_3522_);
                                        crate::leanh::lean_inc(v_val_3524_);
                                        crate::leanh::lean_inc(v_key_3523_);
                                        crate::leanh::lean_dec_ref_known(v_x_3510_, 4);
                                        v_lchild_3547_ =
                                            crate::leanh::lean_ctor_get(v_rchild_3525_, 0);
                                        crate::leanh::lean_inc(v_lchild_3547_);
                                        v_key_3548_ =
                                            crate::leanh::lean_ctor_get(v_rchild_3525_, 1);
                                        crate::leanh::lean_inc(v_key_3548_);
                                        v_val_3549_ =
                                            crate::leanh::lean_ctor_get(v_rchild_3525_, 2);
                                        crate::leanh::lean_inc(v_val_3549_);
                                        v_rchild_3550_ =
                                            crate::leanh::lean_ctor_get(v_rchild_3525_, 3);
                                        crate::leanh::lean_inc(v_rchild_3550_);
                                        crate::leanh::lean_dec_ref_known(v_rchild_3525_, 4);
                                        v_a_3527_ = v_lchild_3522_;
                                        v_kx_3528_ = v_key_3523_;
                                        v_vx_3529_ = v_val_3524_;
                                        v_b_3530_ = v_lchild_3547_;
                                        v_ky_3531_ = v_key_3548_;
                                        v_vy_3532_ = v_val_3549_;
                                        v_c_3533_ = v_rchild_3550_;
                                        v_kz_3534_ = v_x_3511_;
                                        v_vz_3535_ = v_x_3512_;
                                        v_d_3536_ = v_x_3513_;
                                        state = 2;
                                        continue;
                                    } else {
                                        v_a_3515_ = v_x_3510_;
                                        v_kx_3516_ = v_x_3511_;
                                        v_vx_3517_ = v_x_3512_;
                                        v_b_3518_ = v_x_3513_;
                                        state = 1;
                                        continue;
                                    }
                                } else {
                                    v_a_3515_ = v_x_3510_;
                                    v_kx_3516_ = v_x_3511_;
                                    v_vx_3517_ = v_x_3512_;
                                    v_b_3518_ = v_x_3513_;
                                    state = 1;
                                    continue;
                                }
                            }
                        } else {
                            if crate::leanh::lean_obj_tag(v_rchild_3525_) == 1 {
                                v_color_3551_ = crate::leanh::lean_ctor_get_uint8(
                                    v_rchild_3525_,
                                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 4)
                                        as u32,
                                );
                                if v_color_3551_ == 0 {
                                    crate::leanh::lean_inc_ref(v_rchild_3525_);
                                    crate::leanh::lean_inc(v_val_3524_);
                                    crate::leanh::lean_inc(v_key_3523_);
                                    crate::leanh::lean_inc(v_lchild_3522_);
                                    crate::leanh::lean_dec_ref_known(v_x_3510_, 4);
                                    v_lchild_3552_ = crate::leanh::lean_ctor_get(v_rchild_3525_, 0);
                                    crate::leanh::lean_inc(v_lchild_3552_);
                                    v_key_3553_ = crate::leanh::lean_ctor_get(v_rchild_3525_, 1);
                                    crate::leanh::lean_inc(v_key_3553_);
                                    v_val_3554_ = crate::leanh::lean_ctor_get(v_rchild_3525_, 2);
                                    crate::leanh::lean_inc(v_val_3554_);
                                    v_rchild_3555_ = crate::leanh::lean_ctor_get(v_rchild_3525_, 3);
                                    crate::leanh::lean_inc(v_rchild_3555_);
                                    crate::leanh::lean_dec_ref_known(v_rchild_3525_, 4);
                                    v_a_3527_ = v_lchild_3522_;
                                    v_kx_3528_ = v_key_3523_;
                                    v_vx_3529_ = v_val_3524_;
                                    v_b_3530_ = v_lchild_3552_;
                                    v_ky_3531_ = v_key_3553_;
                                    v_vy_3532_ = v_val_3554_;
                                    v_c_3533_ = v_rchild_3555_;
                                    v_kz_3534_ = v_x_3511_;
                                    v_vz_3535_ = v_x_3512_;
                                    v_d_3536_ = v_x_3513_;
                                    state = 2;
                                    continue;
                                } else {
                                    v_a_3515_ = v_x_3510_;
                                    v_kx_3516_ = v_x_3511_;
                                    v_vx_3517_ = v_x_3512_;
                                    v_b_3518_ = v_x_3513_;
                                    state = 1;
                                    continue;
                                }
                            } else {
                                v_a_3515_ = v_x_3510_;
                                v_kx_3516_ = v_x_3511_;
                                v_vx_3517_ = v_x_3512_;
                                v_b_3518_ = v_x_3513_;
                                state = 1;
                                continue;
                            }
                        }
                    } else {
                        v_a_3515_ = v_x_3510_;
                        v_kx_3516_ = v_x_3511_;
                        v_vx_3517_ = v_x_3512_;
                        v_b_3518_ = v_x_3513_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_3515_ = v_x_3510_;
                    v_kx_3516_ = v_x_3511_;
                    v_vx_3517_ = v_x_3512_;
                    v_b_3518_ = v_x_3513_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_3519_ = 1;
                v___x_3520_ = crate::leanh::lean_alloc_ctor(1, 4, (1) as u32);
                crate::leanh::lean_ctor_set(v___x_3520_, 0, v_a_3515_);
                crate::leanh::lean_ctor_set(v___x_3520_, 1, v_kx_3516_);
                crate::leanh::lean_ctor_set(v___x_3520_, 2, v_vx_3517_);
                crate::leanh::lean_ctor_set(v___x_3520_, 3, v_b_3518_);
                crate::leanh::lean_ctor_set_uint8(
                    v___x_3520_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 4) as u32,
                    v___x_3519_,
                );
                return v___x_3520_;
            }
            2 => {
                v___x_3537_ = 1;
                v___x_3538_ = crate::leanh::lean_alloc_ctor(1, 4, (1) as u32);
                crate::leanh::lean_ctor_set(v___x_3538_, 0, v_a_3527_);
                crate::leanh::lean_ctor_set(v___x_3538_, 1, v_kx_3528_);
                crate::leanh::lean_ctor_set(v___x_3538_, 2, v_vx_3529_);
                crate::leanh::lean_ctor_set(v___x_3538_, 3, v_b_3530_);
                crate::leanh::lean_ctor_set_uint8(
                    v___x_3538_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 4) as u32,
                    v___x_3537_,
                );
                v___x_3539_ = crate::leanh::lean_alloc_ctor(1, 4, (1) as u32);
                crate::leanh::lean_ctor_set(v___x_3539_, 0, v_c_3533_);
                crate::leanh::lean_ctor_set(v___x_3539_, 1, v_kz_3534_);
                crate::leanh::lean_ctor_set(v___x_3539_, 2, v_vz_3535_);
                crate::leanh::lean_ctor_set(v___x_3539_, 3, v_d_3536_);
                crate::leanh::lean_ctor_set_uint8(
                    v___x_3539_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 4) as u32,
                    v___x_3537_,
                );
                v___x_3540_ = crate::leanh::lean_alloc_ctor(1, 4, (1) as u32);
                crate::leanh::lean_ctor_set(v___x_3540_, 0, v___x_3538_);
                crate::leanh::lean_ctor_set(v___x_3540_, 1, v_ky_3531_);
                crate::leanh::lean_ctor_set(v___x_3540_, 2, v_vy_3532_);
                crate::leanh::lean_ctor_set(v___x_3540_, 3, v___x_3539_);
                crate::leanh::lean_ctor_set_uint8(
                    v___x_3540_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 4) as u32,
                    v_color_3521_,
                );
                return v___x_3540_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_RBNode_balance2___redArg(
    mut v_x_3556_: *mut crate::leanh::LeanObject,
    mut v_x_3557_: *mut crate::leanh::LeanObject,
    mut v_x_3558_: *mut crate::leanh::LeanObject,
    mut v_x_3559_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_a_3561_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_kx_3562_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_vx_3563_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_b_3564_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3565_: u8 = 0;
    let mut v___x_3566_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_color_3567_: u8 = 0;
    let mut v_lchild_3568_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_key_3569_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_3570_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_rchild_3571_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3573_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_kx_3574_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_vx_3575_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_b_3576_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ky_3577_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_vy_3578_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_c_3579_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_kz_3580_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_vz_3581_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_d_3582_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3583_: u8 = 0;
    let mut v___x_3584_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3585_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3586_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_color_3587_: u8 = 0;
    let mut v_lchild_3588_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_key_3589_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_3590_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_rchild_3591_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_color_3592_: u8 = 0;
    let mut v_lchild_3593_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_key_3594_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_3595_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_rchild_3596_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_color_3597_: u8 = 0;
    let mut v_lchild_3598_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_key_3599_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_3600_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_rchild_3601_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_3559_) == 1 {
                    v_color_3567_ = crate::leanh::lean_ctor_get_uint8(
                        v_x_3559_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 4) as u32,
                    );
                    v_lchild_3568_ = crate::leanh::lean_ctor_get(v_x_3559_, 0);
                    v_key_3569_ = crate::leanh::lean_ctor_get(v_x_3559_, 1);
                    v_val_3570_ = crate::leanh::lean_ctor_get(v_x_3559_, 2);
                    v_rchild_3571_ = crate::leanh::lean_ctor_get(v_x_3559_, 3);
                    if v_color_3567_ == 0 {
                        if crate::leanh::lean_obj_tag(v_lchild_3568_) == 1 {
                            v_color_3587_ = crate::leanh::lean_ctor_get_uint8(
                                v_lchild_3568_,
                                (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 4) as u32,
                            );
                            if v_color_3587_ == 0 {
                                crate::leanh::lean_inc_ref(v_lchild_3568_);
                                crate::leanh::lean_inc(v_rchild_3571_);
                                crate::leanh::lean_inc(v_val_3570_);
                                crate::leanh::lean_inc(v_key_3569_);
                                crate::leanh::lean_dec_ref_known(v_x_3559_, 4);
                                v_lchild_3588_ = crate::leanh::lean_ctor_get(v_lchild_3568_, 0);
                                crate::leanh::lean_inc(v_lchild_3588_);
                                v_key_3589_ = crate::leanh::lean_ctor_get(v_lchild_3568_, 1);
                                crate::leanh::lean_inc(v_key_3589_);
                                v_val_3590_ = crate::leanh::lean_ctor_get(v_lchild_3568_, 2);
                                crate::leanh::lean_inc(v_val_3590_);
                                v_rchild_3591_ = crate::leanh::lean_ctor_get(v_lchild_3568_, 3);
                                crate::leanh::lean_inc(v_rchild_3591_);
                                crate::leanh::lean_dec_ref_known(v_lchild_3568_, 4);
                                v_a_3573_ = v_x_3556_;
                                v_kx_3574_ = v_x_3557_;
                                v_vx_3575_ = v_x_3558_;
                                v_b_3576_ = v_lchild_3588_;
                                v_ky_3577_ = v_key_3589_;
                                v_vy_3578_ = v_val_3590_;
                                v_c_3579_ = v_rchild_3591_;
                                v_kz_3580_ = v_key_3569_;
                                v_vz_3581_ = v_val_3570_;
                                v_d_3582_ = v_rchild_3571_;
                                state = 2;
                                continue;
                            } else {
                                if crate::leanh::lean_obj_tag(v_rchild_3571_) == 1 {
                                    v_color_3592_ = crate::leanh::lean_ctor_get_uint8(
                                        v_rchild_3571_,
                                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 4)
                                            as u32,
                                    );
                                    if v_color_3592_ == 0 {
                                        crate::leanh::lean_inc_ref(v_rchild_3571_);
                                        crate::leanh::lean_inc_ref(v_lchild_3568_);
                                        crate::leanh::lean_inc(v_val_3570_);
                                        crate::leanh::lean_inc(v_key_3569_);
                                        crate::leanh::lean_dec_ref_known(v_x_3559_, 4);
                                        v_lchild_3593_ =
                                            crate::leanh::lean_ctor_get(v_rchild_3571_, 0);
                                        crate::leanh::lean_inc(v_lchild_3593_);
                                        v_key_3594_ =
                                            crate::leanh::lean_ctor_get(v_rchild_3571_, 1);
                                        crate::leanh::lean_inc(v_key_3594_);
                                        v_val_3595_ =
                                            crate::leanh::lean_ctor_get(v_rchild_3571_, 2);
                                        crate::leanh::lean_inc(v_val_3595_);
                                        v_rchild_3596_ =
                                            crate::leanh::lean_ctor_get(v_rchild_3571_, 3);
                                        crate::leanh::lean_inc(v_rchild_3596_);
                                        crate::leanh::lean_dec_ref_known(v_rchild_3571_, 4);
                                        v_a_3573_ = v_x_3556_;
                                        v_kx_3574_ = v_x_3557_;
                                        v_vx_3575_ = v_x_3558_;
                                        v_b_3576_ = v_lchild_3568_;
                                        v_ky_3577_ = v_key_3569_;
                                        v_vy_3578_ = v_val_3570_;
                                        v_c_3579_ = v_lchild_3593_;
                                        v_kz_3580_ = v_key_3594_;
                                        v_vz_3581_ = v_val_3595_;
                                        v_d_3582_ = v_rchild_3596_;
                                        state = 2;
                                        continue;
                                    } else {
                                        v_a_3561_ = v_x_3556_;
                                        v_kx_3562_ = v_x_3557_;
                                        v_vx_3563_ = v_x_3558_;
                                        v_b_3564_ = v_x_3559_;
                                        state = 1;
                                        continue;
                                    }
                                } else {
                                    v_a_3561_ = v_x_3556_;
                                    v_kx_3562_ = v_x_3557_;
                                    v_vx_3563_ = v_x_3558_;
                                    v_b_3564_ = v_x_3559_;
                                    state = 1;
                                    continue;
                                }
                            }
                        } else {
                            if crate::leanh::lean_obj_tag(v_rchild_3571_) == 1 {
                                v_color_3597_ = crate::leanh::lean_ctor_get_uint8(
                                    v_rchild_3571_,
                                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 4)
                                        as u32,
                                );
                                if v_color_3597_ == 0 {
                                    crate::leanh::lean_inc_ref(v_rchild_3571_);
                                    crate::leanh::lean_inc(v_val_3570_);
                                    crate::leanh::lean_inc(v_key_3569_);
                                    crate::leanh::lean_inc(v_lchild_3568_);
                                    crate::leanh::lean_dec_ref_known(v_x_3559_, 4);
                                    v_lchild_3598_ = crate::leanh::lean_ctor_get(v_rchild_3571_, 0);
                                    crate::leanh::lean_inc(v_lchild_3598_);
                                    v_key_3599_ = crate::leanh::lean_ctor_get(v_rchild_3571_, 1);
                                    crate::leanh::lean_inc(v_key_3599_);
                                    v_val_3600_ = crate::leanh::lean_ctor_get(v_rchild_3571_, 2);
                                    crate::leanh::lean_inc(v_val_3600_);
                                    v_rchild_3601_ = crate::leanh::lean_ctor_get(v_rchild_3571_, 3);
                                    crate::leanh::lean_inc(v_rchild_3601_);
                                    crate::leanh::lean_dec_ref_known(v_rchild_3571_, 4);
                                    v_a_3573_ = v_x_3556_;
                                    v_kx_3574_ = v_x_3557_;
                                    v_vx_3575_ = v_x_3558_;
                                    v_b_3576_ = v_lchild_3568_;
                                    v_ky_3577_ = v_key_3569_;
                                    v_vy_3578_ = v_val_3570_;
                                    v_c_3579_ = v_lchild_3598_;
                                    v_kz_3580_ = v_key_3599_;
                                    v_vz_3581_ = v_val_3600_;
                                    v_d_3582_ = v_rchild_3601_;
                                    state = 2;
                                    continue;
                                } else {
                                    v_a_3561_ = v_x_3556_;
                                    v_kx_3562_ = v_x_3557_;
                                    v_vx_3563_ = v_x_3558_;
                                    v_b_3564_ = v_x_3559_;
                                    state = 1;
                                    continue;
                                }
                            } else {
                                v_a_3561_ = v_x_3556_;
                                v_kx_3562_ = v_x_3557_;
                                v_vx_3563_ = v_x_3558_;
                                v_b_3564_ = v_x_3559_;
                                state = 1;
                                continue;
                            }
                        }
                    } else {
                        v_a_3561_ = v_x_3556_;
                        v_kx_3562_ = v_x_3557_;
                        v_vx_3563_ = v_x_3558_;
                        v_b_3564_ = v_x_3559_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_3561_ = v_x_3556_;
                    v_kx_3562_ = v_x_3557_;
                    v_vx_3563_ = v_x_3558_;
                    v_b_3564_ = v_x_3559_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_3565_ = 1;
                v___x_3566_ = crate::leanh::lean_alloc_ctor(1, 4, (1) as u32);
                crate::leanh::lean_ctor_set(v___x_3566_, 0, v_a_3561_);
                crate::leanh::lean_ctor_set(v___x_3566_, 1, v_kx_3562_);
                crate::leanh::lean_ctor_set(v___x_3566_, 2, v_vx_3563_);
                crate::leanh::lean_ctor_set(v___x_3566_, 3, v_b_3564_);
                crate::leanh::lean_ctor_set_uint8(
                    v___x_3566_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 4) as u32,
                    v___x_3565_,
                );
                return v___x_3566_;
            }
            2 => {
                v___x_3583_ = 1;
                v___x_3584_ = crate::leanh::lean_alloc_ctor(1, 4, (1) as u32);
                crate::leanh::lean_ctor_set(v___x_3584_, 0, v_a_3573_);
                crate::leanh::lean_ctor_set(v___x_3584_, 1, v_kx_3574_);
                crate::leanh::lean_ctor_set(v___x_3584_, 2, v_vx_3575_);
                crate::leanh::lean_ctor_set(v___x_3584_, 3, v_b_3576_);
                crate::leanh::lean_ctor_set_uint8(
                    v___x_3584_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 4) as u32,
                    v___x_3583_,
                );
                v___x_3585_ = crate::leanh::lean_alloc_ctor(1, 4, (1) as u32);
                crate::leanh::lean_ctor_set(v___x_3585_, 0, v_c_3579_);
                crate::leanh::lean_ctor_set(v___x_3585_, 1, v_kz_3580_);
                crate::leanh::lean_ctor_set(v___x_3585_, 2, v_vz_3581_);
                crate::leanh::lean_ctor_set(v___x_3585_, 3, v_d_3582_);
                crate::leanh::lean_ctor_set_uint8(
                    v___x_3585_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 4) as u32,
                    v___x_3583_,
                );
                v___x_3586_ = crate::leanh::lean_alloc_ctor(1, 4, (1) as u32);
                crate::leanh::lean_ctor_set(v___x_3586_, 0, v___x_3584_);
                crate::leanh::lean_ctor_set(v___x_3586_, 1, v_ky_3577_);
                crate::leanh::lean_ctor_set(v___x_3586_, 2, v_vy_3578_);
                crate::leanh::lean_ctor_set(v___x_3586_, 3, v___x_3585_);
                crate::leanh::lean_ctor_set_uint8(
                    v___x_3586_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 4) as u32,
                    v_color_3567_,
                );
                return v___x_3586_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_RBNode_balance2(
    mut v_00_u03b1_3602_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_3603_: *mut crate::leanh::LeanObject,
    mut v_x_3604_: *mut crate::leanh::LeanObject,
    mut v_x_3605_: *mut crate::leanh::LeanObject,
    mut v_x_3606_: *mut crate::leanh::LeanObject,
    mut v_x_3607_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_a_3609_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_kx_3610_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_vx_3611_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_b_3612_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3613_: u8 = 0;
    let mut v___x_3614_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_color_3615_: u8 = 0;
    let mut v_lchild_3616_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_key_3617_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_3618_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_rchild_3619_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3621_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_kx_3622_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_vx_3623_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_b_3624_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ky_3625_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_vy_3626_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_c_3627_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_kz_3628_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_vz_3629_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_d_3630_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3631_: u8 = 0;
    let mut v___x_3632_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3633_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3634_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_color_3635_: u8 = 0;
    let mut v_lchild_3636_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_key_3637_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_3638_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_rchild_3639_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_color_3640_: u8 = 0;
    let mut v_lchild_3641_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_key_3642_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_3643_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_rchild_3644_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_color_3645_: u8 = 0;
    let mut v_lchild_3646_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_key_3647_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_3648_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_rchild_3649_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_3607_) == 1 {
                    v_color_3615_ = crate::leanh::lean_ctor_get_uint8(
                        v_x_3607_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 4) as u32,
                    );
                    v_lchild_3616_ = crate::leanh::lean_ctor_get(v_x_3607_, 0);
                    v_key_3617_ = crate::leanh::lean_ctor_get(v_x_3607_, 1);
                    v_val_3618_ = crate::leanh::lean_ctor_get(v_x_3607_, 2);
                    v_rchild_3619_ = crate::leanh::lean_ctor_get(v_x_3607_, 3);
                    if v_color_3615_ == 0 {
                        if crate::leanh::lean_obj_tag(v_lchild_3616_) == 1 {
                            v_color_3635_ = crate::leanh::lean_ctor_get_uint8(
                                v_lchild_3616_,
                                (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 4) as u32,
                            );
                            if v_color_3635_ == 0 {
                                crate::leanh::lean_inc_ref(v_lchild_3616_);
                                crate::leanh::lean_inc(v_rchild_3619_);
                                crate::leanh::lean_inc(v_val_3618_);
                                crate::leanh::lean_inc(v_key_3617_);
                                crate::leanh::lean_dec_ref_known(v_x_3607_, 4);
                                v_lchild_3636_ = crate::leanh::lean_ctor_get(v_lchild_3616_, 0);
                                crate::leanh::lean_inc(v_lchild_3636_);
                                v_key_3637_ = crate::leanh::lean_ctor_get(v_lchild_3616_, 1);
                                crate::leanh::lean_inc(v_key_3637_);
                                v_val_3638_ = crate::leanh::lean_ctor_get(v_lchild_3616_, 2);
                                crate::leanh::lean_inc(v_val_3638_);
                                v_rchild_3639_ = crate::leanh::lean_ctor_get(v_lchild_3616_, 3);
                                crate::leanh::lean_inc(v_rchild_3639_);
                                crate::leanh::lean_dec_ref_known(v_lchild_3616_, 4);
                                v_a_3621_ = v_x_3604_;
                                v_kx_3622_ = v_x_3605_;
                                v_vx_3623_ = v_x_3606_;
                                v_b_3624_ = v_lchild_3636_;
                                v_ky_3625_ = v_key_3637_;
                                v_vy_3626_ = v_val_3638_;
                                v_c_3627_ = v_rchild_3639_;
                                v_kz_3628_ = v_key_3617_;
                                v_vz_3629_ = v_val_3618_;
                                v_d_3630_ = v_rchild_3619_;
                                state = 2;
                                continue;
                            } else {
                                if crate::leanh::lean_obj_tag(v_rchild_3619_) == 1 {
                                    v_color_3640_ = crate::leanh::lean_ctor_get_uint8(
                                        v_rchild_3619_,
                                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 4)
                                            as u32,
                                    );
                                    if v_color_3640_ == 0 {
                                        crate::leanh::lean_inc_ref(v_rchild_3619_);
                                        crate::leanh::lean_inc_ref(v_lchild_3616_);
                                        crate::leanh::lean_inc(v_val_3618_);
                                        crate::leanh::lean_inc(v_key_3617_);
                                        crate::leanh::lean_dec_ref_known(v_x_3607_, 4);
                                        v_lchild_3641_ =
                                            crate::leanh::lean_ctor_get(v_rchild_3619_, 0);
                                        crate::leanh::lean_inc(v_lchild_3641_);
                                        v_key_3642_ =
                                            crate::leanh::lean_ctor_get(v_rchild_3619_, 1);
                                        crate::leanh::lean_inc(v_key_3642_);
                                        v_val_3643_ =
                                            crate::leanh::lean_ctor_get(v_rchild_3619_, 2);
                                        crate::leanh::lean_inc(v_val_3643_);
                                        v_rchild_3644_ =
                                            crate::leanh::lean_ctor_get(v_rchild_3619_, 3);
                                        crate::leanh::lean_inc(v_rchild_3644_);
                                        crate::leanh::lean_dec_ref_known(v_rchild_3619_, 4);
                                        v_a_3621_ = v_x_3604_;
                                        v_kx_3622_ = v_x_3605_;
                                        v_vx_3623_ = v_x_3606_;
                                        v_b_3624_ = v_lchild_3616_;
                                        v_ky_3625_ = v_key_3617_;
                                        v_vy_3626_ = v_val_3618_;
                                        v_c_3627_ = v_lchild_3641_;
                                        v_kz_3628_ = v_key_3642_;
                                        v_vz_3629_ = v_val_3643_;
                                        v_d_3630_ = v_rchild_3644_;
                                        state = 2;
                                        continue;
                                    } else {
                                        v_a_3609_ = v_x_3604_;
                                        v_kx_3610_ = v_x_3605_;
                                        v_vx_3611_ = v_x_3606_;
                                        v_b_3612_ = v_x_3607_;
                                        state = 1;
                                        continue;
                                    }
                                } else {
                                    v_a_3609_ = v_x_3604_;
                                    v_kx_3610_ = v_x_3605_;
                                    v_vx_3611_ = v_x_3606_;
                                    v_b_3612_ = v_x_3607_;
                                    state = 1;
                                    continue;
                                }
                            }
                        } else {
                            if crate::leanh::lean_obj_tag(v_rchild_3619_) == 1 {
                                v_color_3645_ = crate::leanh::lean_ctor_get_uint8(
                                    v_rchild_3619_,
                                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 4)
                                        as u32,
                                );
                                if v_color_3645_ == 0 {
                                    crate::leanh::lean_inc_ref(v_rchild_3619_);
                                    crate::leanh::lean_inc(v_val_3618_);
                                    crate::leanh::lean_inc(v_key_3617_);
                                    crate::leanh::lean_inc(v_lchild_3616_);
                                    crate::leanh::lean_dec_ref_known(v_x_3607_, 4);
                                    v_lchild_3646_ = crate::leanh::lean_ctor_get(v_rchild_3619_, 0);
                                    crate::leanh::lean_inc(v_lchild_3646_);
                                    v_key_3647_ = crate::leanh::lean_ctor_get(v_rchild_3619_, 1);
                                    crate::leanh::lean_inc(v_key_3647_);
                                    v_val_3648_ = crate::leanh::lean_ctor_get(v_rchild_3619_, 2);
                                    crate::leanh::lean_inc(v_val_3648_);
                                    v_rchild_3649_ = crate::leanh::lean_ctor_get(v_rchild_3619_, 3);
                                    crate::leanh::lean_inc(v_rchild_3649_);
                                    crate::leanh::lean_dec_ref_known(v_rchild_3619_, 4);
                                    v_a_3621_ = v_x_3604_;
                                    v_kx_3622_ = v_x_3605_;
                                    v_vx_3623_ = v_x_3606_;
                                    v_b_3624_ = v_lchild_3616_;
                                    v_ky_3625_ = v_key_3617_;
                                    v_vy_3626_ = v_val_3618_;
                                    v_c_3627_ = v_lchild_3646_;
                                    v_kz_3628_ = v_key_3647_;
                                    v_vz_3629_ = v_val_3648_;
                                    v_d_3630_ = v_rchild_3649_;
                                    state = 2;
                                    continue;
                                } else {
                                    v_a_3609_ = v_x_3604_;
                                    v_kx_3610_ = v_x_3605_;
                                    v_vx_3611_ = v_x_3606_;
                                    v_b_3612_ = v_x_3607_;
                                    state = 1;
                                    continue;
                                }
                            } else {
                                v_a_3609_ = v_x_3604_;
                                v_kx_3610_ = v_x_3605_;
                                v_vx_3611_ = v_x_3606_;
                                v_b_3612_ = v_x_3607_;
                                state = 1;
                                continue;
                            }
                        }
                    } else {
                        v_a_3609_ = v_x_3604_;
                        v_kx_3610_ = v_x_3605_;
                        v_vx_3611_ = v_x_3606_;
                        v_b_3612_ = v_x_3607_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_3609_ = v_x_3604_;
                    v_kx_3610_ = v_x_3605_;
                    v_vx_3611_ = v_x_3606_;
                    v_b_3612_ = v_x_3607_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_3613_ = 1;
                v___x_3614_ = crate::leanh::lean_alloc_ctor(1, 4, (1) as u32);
                crate::leanh::lean_ctor_set(v___x_3614_, 0, v_a_3609_);
                crate::leanh::lean_ctor_set(v___x_3614_, 1, v_kx_3610_);
                crate::leanh::lean_ctor_set(v___x_3614_, 2, v_vx_3611_);
                crate::leanh::lean_ctor_set(v___x_3614_, 3, v_b_3612_);
                crate::leanh::lean_ctor_set_uint8(
                    v___x_3614_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 4) as u32,
                    v___x_3613_,
                );
                return v___x_3614_;
            }
            2 => {
                v___x_3631_ = 1;
                v___x_3632_ = crate::leanh::lean_alloc_ctor(1, 4, (1) as u32);
                crate::leanh::lean_ctor_set(v___x_3632_, 0, v_a_3621_);
                crate::leanh::lean_ctor_set(v___x_3632_, 1, v_kx_3622_);
                crate::leanh::lean_ctor_set(v___x_3632_, 2, v_vx_3623_);
                crate::leanh::lean_ctor_set(v___x_3632_, 3, v_b_3624_);
                crate::leanh::lean_ctor_set_uint8(
                    v___x_3632_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 4) as u32,
                    v___x_3631_,
                );
                v___x_3633_ = crate::leanh::lean_alloc_ctor(1, 4, (1) as u32);
                crate::leanh::lean_ctor_set(v___x_3633_, 0, v_c_3627_);
                crate::leanh::lean_ctor_set(v___x_3633_, 1, v_kz_3628_);
                crate::leanh::lean_ctor_set(v___x_3633_, 2, v_vz_3629_);
                crate::leanh::lean_ctor_set(v___x_3633_, 3, v_d_3630_);
                crate::leanh::lean_ctor_set_uint8(
                    v___x_3633_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 4) as u32,
                    v___x_3631_,
                );
                v___x_3634_ = crate::leanh::lean_alloc_ctor(1, 4, (1) as u32);
                crate::leanh::lean_ctor_set(v___x_3634_, 0, v___x_3632_);
                crate::leanh::lean_ctor_set(v___x_3634_, 1, v_ky_3625_);
                crate::leanh::lean_ctor_set(v___x_3634_, 2, v_vy_3626_);
                crate::leanh::lean_ctor_set(v___x_3634_, 3, v___x_3633_);
                crate::leanh::lean_ctor_set_uint8(
                    v___x_3634_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 4) as u32,
                    v_color_3615_,
                );
                return v___x_3634_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_RBNode_isRed___redArg(mut v_x_3650_: *mut crate::leanh::LeanObject) -> u8 {
    if crate::leanh::lean_obj_tag(v_x_3650_) == 1 {
        let mut v_color_3651_: u8 = 0;
        v_color_3651_ = crate::leanh::lean_ctor_get_uint8(
            v_x_3650_,
            (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 4) as u32,
        );
        if v_color_3651_ == 0 {
            let mut v___x_3652_: u8 = 0;
            v___x_3652_ = 1;
            return v___x_3652_;
        } else {
            let mut v___x_3653_: u8 = 0;
            v___x_3653_ = 0;
            return v___x_3653_;
        }
    } else {
        let mut v___x_3654_: u8 = 0;
        v___x_3654_ = 0;
        return v___x_3654_;
    }
}
pub unsafe fn l_Lean_RBNode_isRed___redArg___boxed(
    mut v_x_3655_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3656_: u8 = 0;
    let mut v_r_3657_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3656_ = l_Lean_RBNode_isRed___redArg(v_x_3655_);
    crate::leanh::lean_dec(v_x_3655_);
    v_r_3657_ = crate::leanh::lean_box((v_res_3656_) as usize);
    return v_r_3657_;
}
pub unsafe fn l_Lean_RBNode_isRed(
    mut v_00_u03b1_3658_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_3659_: *mut crate::leanh::LeanObject,
    mut v_x_3660_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_3661_: u8 = 0;
    v___x_3661_ = l_Lean_RBNode_isRed___redArg(v_x_3660_);
    return v___x_3661_;
}
pub unsafe fn l_Lean_RBNode_isRed___boxed(
    mut v_00_u03b1_3662_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_3663_: *mut crate::leanh::LeanObject,
    mut v_x_3664_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3665_: u8 = 0;
    let mut v_r_3666_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3665_ = l_Lean_RBNode_isRed(v_00_u03b1_3662_, v_00_u03b2_3663_, v_x_3664_);
    crate::leanh::lean_dec(v_x_3664_);
    v_r_3666_ = crate::leanh::lean_box((v_res_3665_) as usize);
    return v_r_3666_;
}
pub unsafe fn l_Lean_RBNode_isBlack___redArg(mut v_x_3667_: *mut crate::leanh::LeanObject) -> u8 {
    if crate::leanh::lean_obj_tag(v_x_3667_) == 1 {
        let mut v_color_3668_: u8 = 0;
        v_color_3668_ = crate::leanh::lean_ctor_get_uint8(
            v_x_3667_,
            (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 4) as u32,
        );
        if v_color_3668_ == 1 {
            let mut v___x_3669_: u8 = 0;
            v___x_3669_ = 1;
            return v___x_3669_;
        } else {
            let mut v___x_3670_: u8 = 0;
            v___x_3670_ = 0;
            return v___x_3670_;
        }
    } else {
        let mut v___x_3671_: u8 = 0;
        v___x_3671_ = 0;
        return v___x_3671_;
    }
}
pub unsafe fn l_Lean_RBNode_isBlack___redArg___boxed(
    mut v_x_3672_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3673_: u8 = 0;
    let mut v_r_3674_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3673_ = l_Lean_RBNode_isBlack___redArg(v_x_3672_);
    crate::leanh::lean_dec(v_x_3672_);
    v_r_3674_ = crate::leanh::lean_box((v_res_3673_) as usize);
    return v_r_3674_;
}
pub unsafe fn l_Lean_RBNode_isBlack(
    mut v_00_u03b1_3675_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_3676_: *mut crate::leanh::LeanObject,
    mut v_x_3677_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_3678_: u8 = 0;
    v___x_3678_ = l_Lean_RBNode_isBlack___redArg(v_x_3677_);
    return v___x_3678_;
}
pub unsafe fn l_Lean_RBNode_isBlack___boxed(
    mut v_00_u03b1_3679_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_3680_: *mut crate::leanh::LeanObject,
    mut v_x_3681_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3682_: u8 = 0;
    let mut v_r_3683_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3682_ = l_Lean_RBNode_isBlack(v_00_u03b1_3679_, v_00_u03b2_3680_, v_x_3681_);
    crate::leanh::lean_dec(v_x_3681_);
    v_r_3683_ = crate::leanh::lean_box((v_res_3682_) as usize);
    return v_r_3683_;
}
pub unsafe fn l_Lean_RBNode_ins___redArg(
    mut v_cmp_3684_: *mut crate::leanh::LeanObject,
    mut v_x_3685_: *mut crate::leanh::LeanObject,
    mut v_x_3686_: *mut crate::leanh::LeanObject,
    mut v_x_3687_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3688_: u8 = 0;
    let mut v___x_3689_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_color_3690_: u8 = 0;
    let mut v_lchild_3691_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_key_3692_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_3693_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_rchild_3694_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3696_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3697_: u8 = 0;
    let mut v___x_3698_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3699_: u8 = 0;
    let mut v___x_3700_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3702_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3703_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3705_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3706_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3707_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3709_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3710_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3711_: u8 = 0;
    let mut v_lchild_3712_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_key_3713_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_3714_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_rchild_3715_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3717_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3718_: u8 = 0;
    let mut v___x_3719_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3720_: u8 = 0;
    let mut v___x_3721_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_color_3722_: u8 = 0;
    let mut v_lchild_3723_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_key_3724_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_3725_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_rchild_3726_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3728_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_kx_3729_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_vx_3730_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_b_3731_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ky_3732_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_vy_3733_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_c_3734_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_kz_3735_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_vz_3736_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_d_3737_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3739_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3740_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3741_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3742_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_color_3743_: u8 = 0;
    let mut v_lchild_3744_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_key_3745_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_3746_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_rchild_3747_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_color_3748_: u8 = 0;
    let mut v_lchild_3749_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_key_3750_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_3751_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_rchild_3752_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3754_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3755_: u8 = 0;
    let mut v___x_3757_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3758_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3759_: u8 = 0;
    let mut v_unused_3760_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_3761_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_3762_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_3763_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3765_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3766_: u8 = 0;
    let mut v___x_3768_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3769_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3770_: u8 = 0;
    let mut v_unused_3771_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_3772_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_3773_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_3774_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_color_3775_: u8 = 0;
    let mut v_lchild_3776_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_key_3777_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_3778_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_rchild_3779_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3781_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3782_: u8 = 0;
    let mut v___x_3784_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3785_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3786_: u8 = 0;
    let mut v_unused_3787_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_3788_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_3789_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_3790_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3791_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3792_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3794_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3795_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3797_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3798_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3799_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_color_3800_: u8 = 0;
    let mut v_lchild_3801_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_key_3802_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_3803_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_rchild_3804_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3806_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_kx_3807_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_vx_3808_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_b_3809_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ky_3810_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_vy_3811_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_c_3812_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_kz_3813_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_vz_3814_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_d_3815_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3817_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3818_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3819_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3820_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_color_3821_: u8 = 0;
    let mut v_lchild_3822_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_key_3823_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_3824_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_rchild_3825_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_color_3826_: u8 = 0;
    let mut v_lchild_3827_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_key_3828_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_3829_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_rchild_3830_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3832_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3833_: u8 = 0;
    let mut v___x_3835_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3836_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3837_: u8 = 0;
    let mut v_unused_3838_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_3839_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_3840_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_3841_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3843_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3844_: u8 = 0;
    let mut v___x_3846_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3847_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3848_: u8 = 0;
    let mut v_unused_3849_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_3850_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_3851_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_3852_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_color_3853_: u8 = 0;
    let mut v_lchild_3854_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_key_3855_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_3856_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_rchild_3857_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3859_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3860_: u8 = 0;
    let mut v___x_3862_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3863_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3864_: u8 = 0;
    let mut v_unused_3865_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_3866_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_3867_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_3868_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3869_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3870_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3872_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3873_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3874_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_3685_) == 0 {
                    crate::leanh::lean_dec_ref(v_cmp_3684_);
                    v___x_3688_ = 0;
                    v___x_3689_ = crate::leanh::lean_alloc_ctor(1, 4, (1) as u32);
                    crate::leanh::lean_ctor_set(v___x_3689_, 0, v_x_3685_);
                    crate::leanh::lean_ctor_set(v___x_3689_, 1, v_x_3686_);
                    crate::leanh::lean_ctor_set(v___x_3689_, 2, v_x_3687_);
                    crate::leanh::lean_ctor_set(v___x_3689_, 3, v_x_3685_);
                    crate::leanh::lean_ctor_set_uint8(
                        v___x_3689_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 4) as u32,
                        v___x_3688_,
                    );
                    return v___x_3689_;
                } else {
                    v_color_3690_ = crate::leanh::lean_ctor_get_uint8(
                        v_x_3685_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 4) as u32,
                    );
                    if v_color_3690_ == 0 {
                        v_lchild_3691_ = crate::leanh::lean_ctor_get(v_x_3685_, 0);
                        v_key_3692_ = crate::leanh::lean_ctor_get(v_x_3685_, 1);
                        v_val_3693_ = crate::leanh::lean_ctor_get(v_x_3685_, 2);
                        v_rchild_3694_ = crate::leanh::lean_ctor_get(v_x_3685_, 3);
                        v_isSharedCheck_3711_ = (!crate::leanh::lean_is_exclusive(v_x_3685_)) as u8;
                        if v_isSharedCheck_3711_ == 0 {
                            v___x_3696_ = v_x_3685_;
                            v_isShared_3697_ = v_isSharedCheck_3711_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_rchild_3694_);
                            crate::leanh::lean_inc(v_val_3693_);
                            crate::leanh::lean_inc(v_key_3692_);
                            crate::leanh::lean_inc(v_lchild_3691_);
                            crate::leanh::lean_dec(v_x_3685_);
                            v___x_3696_ = crate::leanh::lean_box(0);
                            v_isShared_3697_ = v_isSharedCheck_3711_;
                            state = 1;
                            continue;
                        }
                    } else {
                        v_lchild_3712_ = crate::leanh::lean_ctor_get(v_x_3685_, 0);
                        v_key_3713_ = crate::leanh::lean_ctor_get(v_x_3685_, 1);
                        v_val_3714_ = crate::leanh::lean_ctor_get(v_x_3685_, 2);
                        v_rchild_3715_ = crate::leanh::lean_ctor_get(v_x_3685_, 3);
                        v_isSharedCheck_3874_ = (!crate::leanh::lean_is_exclusive(v_x_3685_)) as u8;
                        if v_isSharedCheck_3874_ == 0 {
                            v___x_3717_ = v_x_3685_;
                            v_isShared_3718_ = v_isSharedCheck_3874_;
                            state = 5;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_rchild_3715_);
                            crate::leanh::lean_inc(v_val_3714_);
                            crate::leanh::lean_inc(v_key_3713_);
                            crate::leanh::lean_inc(v_lchild_3712_);
                            crate::leanh::lean_dec(v_x_3685_);
                            v___x_3717_ = crate::leanh::lean_box(0);
                            v_isShared_3718_ = v_isSharedCheck_3874_;
                            state = 5;
                            continue;
                        }
                    }
                }
            }
            1 => {
                crate::leanh::lean_inc_ref(v_cmp_3684_);
                crate::leanh::lean_inc(v_key_3692_);
                crate::leanh::lean_inc(v_x_3686_);
                v___x_3698_ = crate::leanh::lean_apply_2(v_cmp_3684_, v_x_3686_, v_key_3692_);
                v___x_3699_ = (crate::leanh::lean_unbox(v___x_3698_) as u8);
                match v___x_3699_ {
                    0 => {
                        v___x_3700_ = l_Lean_RBNode_ins___redArg(
                            v_cmp_3684_,
                            v_lchild_3691_,
                            v_x_3686_,
                            v_x_3687_,
                        );
                        if v_isShared_3697_ == 0 {
                            crate::leanh::lean_ctor_set(v___x_3696_, 0, v___x_3700_);
                            v___x_3702_ = v___x_3696_;
                            state = 2;
                            continue;
                        } else {
                            v_reuseFailAlloc_3703_ =
                                crate::leanh::lean_alloc_ctor(1, 4, (1) as u32);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_3703_, 0, v___x_3700_);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_3703_, 1, v_key_3692_);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_3703_, 2, v_val_3693_);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_3703_, 3, v_rchild_3694_);
                            crate::leanh::lean_ctor_set_uint8(
                                v_reuseFailAlloc_3703_,
                                (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 4) as u32,
                                v_color_3690_,
                            );
                            v___x_3702_ = v_reuseFailAlloc_3703_;
                            state = 2;
                            continue;
                        }
                    }
                    1 => {
                        crate::leanh::lean_dec(v_val_3693_);
                        crate::leanh::lean_dec(v_key_3692_);
                        crate::leanh::lean_dec_ref(v_cmp_3684_);
                        if v_isShared_3697_ == 0 {
                            crate::leanh::lean_ctor_set(v___x_3696_, 2, v_x_3687_);
                            crate::leanh::lean_ctor_set(v___x_3696_, 1, v_x_3686_);
                            v___x_3705_ = v___x_3696_;
                            state = 3;
                            continue;
                        } else {
                            v_reuseFailAlloc_3706_ =
                                crate::leanh::lean_alloc_ctor(1, 4, (1) as u32);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_3706_, 0, v_lchild_3691_);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_3706_, 1, v_x_3686_);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_3706_, 2, v_x_3687_);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_3706_, 3, v_rchild_3694_);
                            crate::leanh::lean_ctor_set_uint8(
                                v_reuseFailAlloc_3706_,
                                (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 4) as u32,
                                v_color_3690_,
                            );
                            v___x_3705_ = v_reuseFailAlloc_3706_;
                            state = 3;
                            continue;
                        }
                    }
                    _ => {
                        v___x_3707_ = l_Lean_RBNode_ins___redArg(
                            v_cmp_3684_,
                            v_rchild_3694_,
                            v_x_3686_,
                            v_x_3687_,
                        );
                        if v_isShared_3697_ == 0 {
                            crate::leanh::lean_ctor_set(v___x_3696_, 3, v___x_3707_);
                            v___x_3709_ = v___x_3696_;
                            state = 4;
                            continue;
                        } else {
                            v_reuseFailAlloc_3710_ =
                                crate::leanh::lean_alloc_ctor(1, 4, (1) as u32);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_3710_, 0, v_lchild_3691_);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_3710_, 1, v_key_3692_);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_3710_, 2, v_val_3693_);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_3710_, 3, v___x_3707_);
                            crate::leanh::lean_ctor_set_uint8(
                                v_reuseFailAlloc_3710_,
                                (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 4) as u32,
                                v_color_3690_,
                            );
                            v___x_3709_ = v_reuseFailAlloc_3710_;
                            state = 4;
                            continue;
                        }
                    }
                }
            }
            2 => {
                return v___x_3702_;
            }
            3 => {
                return v___x_3705_;
            }
            4 => {
                return v___x_3709_;
            }
            5 => {
                crate::leanh::lean_inc_ref(v_cmp_3684_);
                crate::leanh::lean_inc(v_key_3713_);
                crate::leanh::lean_inc(v_x_3686_);
                v___x_3719_ = crate::leanh::lean_apply_2(v_cmp_3684_, v_x_3686_, v_key_3713_);
                v___x_3720_ = (crate::leanh::lean_unbox(v___x_3719_) as u8);
                match v___x_3720_ {
                    0 => {
                        v___x_3721_ = l_Lean_RBNode_ins___redArg(
                            v_cmp_3684_,
                            v_lchild_3712_,
                            v_x_3686_,
                            v_x_3687_,
                        );
                        if crate::leanh::lean_obj_tag(v___x_3721_) == 1 {
                            v_color_3722_ = crate::leanh::lean_ctor_get_uint8(
                                v___x_3721_,
                                (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 4) as u32,
                            );
                            v_lchild_3723_ = crate::leanh::lean_ctor_get(v___x_3721_, 0);
                            crate::leanh::lean_inc(v_lchild_3723_);
                            v_key_3724_ = crate::leanh::lean_ctor_get(v___x_3721_, 1);
                            crate::leanh::lean_inc(v_key_3724_);
                            v_val_3725_ = crate::leanh::lean_ctor_get(v___x_3721_, 2);
                            crate::leanh::lean_inc(v_val_3725_);
                            v_rchild_3726_ = crate::leanh::lean_ctor_get(v___x_3721_, 3);
                            crate::leanh::lean_inc(v_rchild_3726_);
                            if v_color_3722_ == 0 {
                                if crate::leanh::lean_obj_tag(v_lchild_3723_) == 1 {
                                    v_color_3743_ = crate::leanh::lean_ctor_get_uint8(
                                        v_lchild_3723_,
                                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 4)
                                            as u32,
                                    );
                                    if v_color_3743_ == 0 {
                                        crate::leanh::lean_dec_ref_known(v___x_3721_, 4);
                                        v_lchild_3744_ =
                                            crate::leanh::lean_ctor_get(v_lchild_3723_, 0);
                                        crate::leanh::lean_inc(v_lchild_3744_);
                                        v_key_3745_ =
                                            crate::leanh::lean_ctor_get(v_lchild_3723_, 1);
                                        crate::leanh::lean_inc(v_key_3745_);
                                        v_val_3746_ =
                                            crate::leanh::lean_ctor_get(v_lchild_3723_, 2);
                                        crate::leanh::lean_inc(v_val_3746_);
                                        v_rchild_3747_ =
                                            crate::leanh::lean_ctor_get(v_lchild_3723_, 3);
                                        crate::leanh::lean_inc(v_rchild_3747_);
                                        crate::leanh::lean_dec_ref_known(v_lchild_3723_, 4);
                                        v_a_3728_ = v_lchild_3744_;
                                        v_kx_3729_ = v_key_3745_;
                                        v_vx_3730_ = v_val_3746_;
                                        v_b_3731_ = v_rchild_3747_;
                                        v_ky_3732_ = v_key_3724_;
                                        v_vy_3733_ = v_val_3725_;
                                        v_c_3734_ = v_rchild_3726_;
                                        v_kz_3735_ = v_key_3713_;
                                        v_vz_3736_ = v_val_3714_;
                                        v_d_3737_ = v_rchild_3715_;
                                        state = 6;
                                        continue;
                                    } else {
                                        if crate::leanh::lean_obj_tag(v_rchild_3726_) == 1 {
                                            v_color_3748_ = crate::leanh::lean_ctor_get_uint8(
                                                v_rchild_3726_,
                                                (core::mem::size_of::<*mut crate::leanh::LeanObject>(
                                                ) * 4)
                                                    as u32,
                                            );
                                            if v_color_3748_ == 0 {
                                                crate::leanh::lean_dec_ref_known(v___x_3721_, 4);
                                                v_lchild_3749_ =
                                                    crate::leanh::lean_ctor_get(v_rchild_3726_, 0);
                                                crate::leanh::lean_inc(v_lchild_3749_);
                                                v_key_3750_ =
                                                    crate::leanh::lean_ctor_get(v_rchild_3726_, 1);
                                                crate::leanh::lean_inc(v_key_3750_);
                                                v_val_3751_ =
                                                    crate::leanh::lean_ctor_get(v_rchild_3726_, 2);
                                                crate::leanh::lean_inc(v_val_3751_);
                                                v_rchild_3752_ =
                                                    crate::leanh::lean_ctor_get(v_rchild_3726_, 3);
                                                crate::leanh::lean_inc(v_rchild_3752_);
                                                crate::leanh::lean_dec_ref_known(v_rchild_3726_, 4);
                                                v_a_3728_ = v_lchild_3723_;
                                                v_kx_3729_ = v_key_3724_;
                                                v_vx_3730_ = v_val_3725_;
                                                v_b_3731_ = v_lchild_3749_;
                                                v_ky_3732_ = v_key_3750_;
                                                v_vy_3733_ = v_val_3751_;
                                                v_c_3734_ = v_rchild_3752_;
                                                v_kz_3735_ = v_key_3713_;
                                                v_vz_3736_ = v_val_3714_;
                                                v_d_3737_ = v_rchild_3715_;
                                                state = 6;
                                                continue;
                                            } else {
                                                crate::leanh::lean_dec_ref_known(v_lchild_3723_, 4);
                                                crate::leanh::lean_dec(v_val_3725_);
                                                crate::leanh::lean_dec(v_key_3724_);
                                                crate::leanh::lean_del_object(v___x_3717_);
                                                v_isSharedCheck_3759_ =
                                                    (!crate::leanh::lean_is_exclusive(
                                                        v_rchild_3726_,
                                                    ))
                                                        as u8;
                                                if v_isSharedCheck_3759_ == 0 {
                                                    v_unused_3760_ = crate::leanh::lean_ctor_get(
                                                        v_rchild_3726_,
                                                        3,
                                                    );
                                                    crate::leanh::lean_dec(v_unused_3760_);
                                                    v_unused_3761_ = crate::leanh::lean_ctor_get(
                                                        v_rchild_3726_,
                                                        2,
                                                    );
                                                    crate::leanh::lean_dec(v_unused_3761_);
                                                    v_unused_3762_ = crate::leanh::lean_ctor_get(
                                                        v_rchild_3726_,
                                                        1,
                                                    );
                                                    crate::leanh::lean_dec(v_unused_3762_);
                                                    v_unused_3763_ = crate::leanh::lean_ctor_get(
                                                        v_rchild_3726_,
                                                        0,
                                                    );
                                                    crate::leanh::lean_dec(v_unused_3763_);
                                                    v___x_3754_ = v_rchild_3726_;
                                                    v_isShared_3755_ = v_isSharedCheck_3759_;
                                                    state = 8;
                                                    continue;
                                                } else {
                                                    crate::leanh::lean_dec(v_rchild_3726_);
                                                    v___x_3754_ = crate::leanh::lean_box(0);
                                                    v_isShared_3755_ = v_isSharedCheck_3759_;
                                                    state = 8;
                                                    continue;
                                                }
                                            }
                                        } else {
                                            crate::leanh::lean_dec(v_rchild_3726_);
                                            crate::leanh::lean_dec(v_val_3725_);
                                            crate::leanh::lean_dec(v_key_3724_);
                                            crate::leanh::lean_del_object(v___x_3717_);
                                            v_isSharedCheck_3770_ =
                                                (!crate::leanh::lean_is_exclusive(v_lchild_3723_))
                                                    as u8;
                                            if v_isSharedCheck_3770_ == 0 {
                                                v_unused_3771_ =
                                                    crate::leanh::lean_ctor_get(v_lchild_3723_, 3);
                                                crate::leanh::lean_dec(v_unused_3771_);
                                                v_unused_3772_ =
                                                    crate::leanh::lean_ctor_get(v_lchild_3723_, 2);
                                                crate::leanh::lean_dec(v_unused_3772_);
                                                v_unused_3773_ =
                                                    crate::leanh::lean_ctor_get(v_lchild_3723_, 1);
                                                crate::leanh::lean_dec(v_unused_3773_);
                                                v_unused_3774_ =
                                                    crate::leanh::lean_ctor_get(v_lchild_3723_, 0);
                                                crate::leanh::lean_dec(v_unused_3774_);
                                                v___x_3765_ = v_lchild_3723_;
                                                v_isShared_3766_ = v_isSharedCheck_3770_;
                                                state = 10;
                                                continue;
                                            } else {
                                                crate::leanh::lean_dec(v_lchild_3723_);
                                                v___x_3765_ = crate::leanh::lean_box(0);
                                                v_isShared_3766_ = v_isSharedCheck_3770_;
                                                state = 10;
                                                continue;
                                            }
                                        }
                                    }
                                } else {
                                    if crate::leanh::lean_obj_tag(v_rchild_3726_) == 1 {
                                        v_color_3775_ = crate::leanh::lean_ctor_get_uint8(
                                            v_rchild_3726_,
                                            (core::mem::size_of::<*mut crate::leanh::LeanObject>()
                                                * 4)
                                                as u32,
                                        );
                                        if v_color_3775_ == 0 {
                                            crate::leanh::lean_dec_ref_known(v___x_3721_, 4);
                                            v_lchild_3776_ =
                                                crate::leanh::lean_ctor_get(v_rchild_3726_, 0);
                                            crate::leanh::lean_inc(v_lchild_3776_);
                                            v_key_3777_ =
                                                crate::leanh::lean_ctor_get(v_rchild_3726_, 1);
                                            crate::leanh::lean_inc(v_key_3777_);
                                            v_val_3778_ =
                                                crate::leanh::lean_ctor_get(v_rchild_3726_, 2);
                                            crate::leanh::lean_inc(v_val_3778_);
                                            v_rchild_3779_ =
                                                crate::leanh::lean_ctor_get(v_rchild_3726_, 3);
                                            crate::leanh::lean_inc(v_rchild_3779_);
                                            crate::leanh::lean_dec_ref_known(v_rchild_3726_, 4);
                                            v_a_3728_ = v_lchild_3723_;
                                            v_kx_3729_ = v_key_3724_;
                                            v_vx_3730_ = v_val_3725_;
                                            v_b_3731_ = v_lchild_3776_;
                                            v_ky_3732_ = v_key_3777_;
                                            v_vy_3733_ = v_val_3778_;
                                            v_c_3734_ = v_rchild_3779_;
                                            v_kz_3735_ = v_key_3713_;
                                            v_vz_3736_ = v_val_3714_;
                                            v_d_3737_ = v_rchild_3715_;
                                            state = 6;
                                            continue;
                                        } else {
                                            crate::leanh::lean_dec(v_val_3725_);
                                            crate::leanh::lean_dec(v_key_3724_);
                                            crate::leanh::lean_dec(v_lchild_3723_);
                                            crate::leanh::lean_del_object(v___x_3717_);
                                            v_isSharedCheck_3786_ =
                                                (!crate::leanh::lean_is_exclusive(v_rchild_3726_))
                                                    as u8;
                                            if v_isSharedCheck_3786_ == 0 {
                                                v_unused_3787_ =
                                                    crate::leanh::lean_ctor_get(v_rchild_3726_, 3);
                                                crate::leanh::lean_dec(v_unused_3787_);
                                                v_unused_3788_ =
                                                    crate::leanh::lean_ctor_get(v_rchild_3726_, 2);
                                                crate::leanh::lean_dec(v_unused_3788_);
                                                v_unused_3789_ =
                                                    crate::leanh::lean_ctor_get(v_rchild_3726_, 1);
                                                crate::leanh::lean_dec(v_unused_3789_);
                                                v_unused_3790_ =
                                                    crate::leanh::lean_ctor_get(v_rchild_3726_, 0);
                                                crate::leanh::lean_dec(v_unused_3790_);
                                                v___x_3781_ = v_rchild_3726_;
                                                v_isShared_3782_ = v_isSharedCheck_3786_;
                                                state = 12;
                                                continue;
                                            } else {
                                                crate::leanh::lean_dec(v_rchild_3726_);
                                                v___x_3781_ = crate::leanh::lean_box(0);
                                                v_isShared_3782_ = v_isSharedCheck_3786_;
                                                state = 12;
                                                continue;
                                            }
                                        }
                                    } else {
                                        crate::leanh::lean_dec(v_rchild_3726_);
                                        crate::leanh::lean_dec(v_val_3725_);
                                        crate::leanh::lean_dec(v_key_3724_);
                                        crate::leanh::lean_dec(v_lchild_3723_);
                                        crate::leanh::lean_del_object(v___x_3717_);
                                        v___x_3791_ =
                                            crate::leanh::lean_alloc_ctor(1, 4, (1) as u32);
                                        crate::leanh::lean_ctor_set(v___x_3791_, 0, v___x_3721_);
                                        crate::leanh::lean_ctor_set(v___x_3791_, 1, v_key_3713_);
                                        crate::leanh::lean_ctor_set(v___x_3791_, 2, v_val_3714_);
                                        crate::leanh::lean_ctor_set(v___x_3791_, 3, v_rchild_3715_);
                                        crate::leanh::lean_ctor_set_uint8(
                                            v___x_3791_,
                                            (core::mem::size_of::<*mut crate::leanh::LeanObject>()
                                                * 4)
                                                as u32,
                                            v_color_3690_,
                                        );
                                        return v___x_3791_;
                                    }
                                }
                            } else {
                                crate::leanh::lean_dec(v_rchild_3726_);
                                crate::leanh::lean_dec(v_val_3725_);
                                crate::leanh::lean_dec(v_key_3724_);
                                crate::leanh::lean_dec(v_lchild_3723_);
                                crate::leanh::lean_del_object(v___x_3717_);
                                v___x_3792_ = crate::leanh::lean_alloc_ctor(1, 4, (1) as u32);
                                crate::leanh::lean_ctor_set(v___x_3792_, 0, v___x_3721_);
                                crate::leanh::lean_ctor_set(v___x_3792_, 1, v_key_3713_);
                                crate::leanh::lean_ctor_set(v___x_3792_, 2, v_val_3714_);
                                crate::leanh::lean_ctor_set(v___x_3792_, 3, v_rchild_3715_);
                                crate::leanh::lean_ctor_set_uint8(
                                    v___x_3792_,
                                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 4)
                                        as u32,
                                    v_color_3690_,
                                );
                                return v___x_3792_;
                            }
                        } else {
                            if v_isShared_3718_ == 0 {
                                crate::leanh::lean_ctor_set(v___x_3717_, 0, v___x_3721_);
                                v___x_3794_ = v___x_3717_;
                                state = 14;
                                continue;
                            } else {
                                v_reuseFailAlloc_3795_ =
                                    crate::leanh::lean_alloc_ctor(1, 4, (1) as u32);
                                crate::leanh::lean_ctor_set(v_reuseFailAlloc_3795_, 0, v___x_3721_);
                                crate::leanh::lean_ctor_set(v_reuseFailAlloc_3795_, 1, v_key_3713_);
                                crate::leanh::lean_ctor_set(v_reuseFailAlloc_3795_, 2, v_val_3714_);
                                crate::leanh::lean_ctor_set(
                                    v_reuseFailAlloc_3795_,
                                    3,
                                    v_rchild_3715_,
                                );
                                crate::leanh::lean_ctor_set_uint8(
                                    v_reuseFailAlloc_3795_,
                                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 4)
                                        as u32,
                                    v_color_3690_,
                                );
                                v___x_3794_ = v_reuseFailAlloc_3795_;
                                state = 14;
                                continue;
                            }
                        }
                    }
                    1 => {
                        crate::leanh::lean_dec(v_val_3714_);
                        crate::leanh::lean_dec(v_key_3713_);
                        crate::leanh::lean_dec_ref(v_cmp_3684_);
                        if v_isShared_3718_ == 0 {
                            crate::leanh::lean_ctor_set(v___x_3717_, 2, v_x_3687_);
                            crate::leanh::lean_ctor_set(v___x_3717_, 1, v_x_3686_);
                            v___x_3797_ = v___x_3717_;
                            state = 15;
                            continue;
                        } else {
                            v_reuseFailAlloc_3798_ =
                                crate::leanh::lean_alloc_ctor(1, 4, (1) as u32);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_3798_, 0, v_lchild_3712_);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_3798_, 1, v_x_3686_);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_3798_, 2, v_x_3687_);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_3798_, 3, v_rchild_3715_);
                            crate::leanh::lean_ctor_set_uint8(
                                v_reuseFailAlloc_3798_,
                                (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 4) as u32,
                                v_color_3690_,
                            );
                            v___x_3797_ = v_reuseFailAlloc_3798_;
                            state = 15;
                            continue;
                        }
                    }
                    _ => {
                        v___x_3799_ = l_Lean_RBNode_ins___redArg(
                            v_cmp_3684_,
                            v_rchild_3715_,
                            v_x_3686_,
                            v_x_3687_,
                        );
                        if crate::leanh::lean_obj_tag(v___x_3799_) == 1 {
                            v_color_3800_ = crate::leanh::lean_ctor_get_uint8(
                                v___x_3799_,
                                (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 4) as u32,
                            );
                            v_lchild_3801_ = crate::leanh::lean_ctor_get(v___x_3799_, 0);
                            crate::leanh::lean_inc(v_lchild_3801_);
                            v_key_3802_ = crate::leanh::lean_ctor_get(v___x_3799_, 1);
                            crate::leanh::lean_inc(v_key_3802_);
                            v_val_3803_ = crate::leanh::lean_ctor_get(v___x_3799_, 2);
                            crate::leanh::lean_inc(v_val_3803_);
                            v_rchild_3804_ = crate::leanh::lean_ctor_get(v___x_3799_, 3);
                            crate::leanh::lean_inc(v_rchild_3804_);
                            if v_color_3800_ == 0 {
                                if crate::leanh::lean_obj_tag(v_lchild_3801_) == 1 {
                                    v_color_3821_ = crate::leanh::lean_ctor_get_uint8(
                                        v_lchild_3801_,
                                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 4)
                                            as u32,
                                    );
                                    if v_color_3821_ == 0 {
                                        crate::leanh::lean_dec_ref_known(v___x_3799_, 4);
                                        v_lchild_3822_ =
                                            crate::leanh::lean_ctor_get(v_lchild_3801_, 0);
                                        crate::leanh::lean_inc(v_lchild_3822_);
                                        v_key_3823_ =
                                            crate::leanh::lean_ctor_get(v_lchild_3801_, 1);
                                        crate::leanh::lean_inc(v_key_3823_);
                                        v_val_3824_ =
                                            crate::leanh::lean_ctor_get(v_lchild_3801_, 2);
                                        crate::leanh::lean_inc(v_val_3824_);
                                        v_rchild_3825_ =
                                            crate::leanh::lean_ctor_get(v_lchild_3801_, 3);
                                        crate::leanh::lean_inc(v_rchild_3825_);
                                        crate::leanh::lean_dec_ref_known(v_lchild_3801_, 4);
                                        v_a_3806_ = v_lchild_3712_;
                                        v_kx_3807_ = v_key_3713_;
                                        v_vx_3808_ = v_val_3714_;
                                        v_b_3809_ = v_lchild_3822_;
                                        v_ky_3810_ = v_key_3823_;
                                        v_vy_3811_ = v_val_3824_;
                                        v_c_3812_ = v_rchild_3825_;
                                        v_kz_3813_ = v_key_3802_;
                                        v_vz_3814_ = v_val_3803_;
                                        v_d_3815_ = v_rchild_3804_;
                                        state = 16;
                                        continue;
                                    } else {
                                        if crate::leanh::lean_obj_tag(v_rchild_3804_) == 1 {
                                            v_color_3826_ = crate::leanh::lean_ctor_get_uint8(
                                                v_rchild_3804_,
                                                (core::mem::size_of::<*mut crate::leanh::LeanObject>(
                                                ) * 4)
                                                    as u32,
                                            );
                                            if v_color_3826_ == 0 {
                                                crate::leanh::lean_dec_ref_known(v___x_3799_, 4);
                                                v_lchild_3827_ =
                                                    crate::leanh::lean_ctor_get(v_rchild_3804_, 0);
                                                crate::leanh::lean_inc(v_lchild_3827_);
                                                v_key_3828_ =
                                                    crate::leanh::lean_ctor_get(v_rchild_3804_, 1);
                                                crate::leanh::lean_inc(v_key_3828_);
                                                v_val_3829_ =
                                                    crate::leanh::lean_ctor_get(v_rchild_3804_, 2);
                                                crate::leanh::lean_inc(v_val_3829_);
                                                v_rchild_3830_ =
                                                    crate::leanh::lean_ctor_get(v_rchild_3804_, 3);
                                                crate::leanh::lean_inc(v_rchild_3830_);
                                                crate::leanh::lean_dec_ref_known(v_rchild_3804_, 4);
                                                v_a_3806_ = v_lchild_3712_;
                                                v_kx_3807_ = v_key_3713_;
                                                v_vx_3808_ = v_val_3714_;
                                                v_b_3809_ = v_lchild_3801_;
                                                v_ky_3810_ = v_key_3802_;
                                                v_vy_3811_ = v_val_3803_;
                                                v_c_3812_ = v_lchild_3827_;
                                                v_kz_3813_ = v_key_3828_;
                                                v_vz_3814_ = v_val_3829_;
                                                v_d_3815_ = v_rchild_3830_;
                                                state = 16;
                                                continue;
                                            } else {
                                                crate::leanh::lean_dec_ref_known(v_lchild_3801_, 4);
                                                crate::leanh::lean_dec(v_val_3803_);
                                                crate::leanh::lean_dec(v_key_3802_);
                                                crate::leanh::lean_del_object(v___x_3717_);
                                                v_isSharedCheck_3837_ =
                                                    (!crate::leanh::lean_is_exclusive(
                                                        v_rchild_3804_,
                                                    ))
                                                        as u8;
                                                if v_isSharedCheck_3837_ == 0 {
                                                    v_unused_3838_ = crate::leanh::lean_ctor_get(
                                                        v_rchild_3804_,
                                                        3,
                                                    );
                                                    crate::leanh::lean_dec(v_unused_3838_);
                                                    v_unused_3839_ = crate::leanh::lean_ctor_get(
                                                        v_rchild_3804_,
                                                        2,
                                                    );
                                                    crate::leanh::lean_dec(v_unused_3839_);
                                                    v_unused_3840_ = crate::leanh::lean_ctor_get(
                                                        v_rchild_3804_,
                                                        1,
                                                    );
                                                    crate::leanh::lean_dec(v_unused_3840_);
                                                    v_unused_3841_ = crate::leanh::lean_ctor_get(
                                                        v_rchild_3804_,
                                                        0,
                                                    );
                                                    crate::leanh::lean_dec(v_unused_3841_);
                                                    v___x_3832_ = v_rchild_3804_;
                                                    v_isShared_3833_ = v_isSharedCheck_3837_;
                                                    state = 18;
                                                    continue;
                                                } else {
                                                    crate::leanh::lean_dec(v_rchild_3804_);
                                                    v___x_3832_ = crate::leanh::lean_box(0);
                                                    v_isShared_3833_ = v_isSharedCheck_3837_;
                                                    state = 18;
                                                    continue;
                                                }
                                            }
                                        } else {
                                            crate::leanh::lean_dec(v_rchild_3804_);
                                            crate::leanh::lean_dec(v_val_3803_);
                                            crate::leanh::lean_dec(v_key_3802_);
                                            crate::leanh::lean_del_object(v___x_3717_);
                                            v_isSharedCheck_3848_ =
                                                (!crate::leanh::lean_is_exclusive(v_lchild_3801_))
                                                    as u8;
                                            if v_isSharedCheck_3848_ == 0 {
                                                v_unused_3849_ =
                                                    crate::leanh::lean_ctor_get(v_lchild_3801_, 3);
                                                crate::leanh::lean_dec(v_unused_3849_);
                                                v_unused_3850_ =
                                                    crate::leanh::lean_ctor_get(v_lchild_3801_, 2);
                                                crate::leanh::lean_dec(v_unused_3850_);
                                                v_unused_3851_ =
                                                    crate::leanh::lean_ctor_get(v_lchild_3801_, 1);
                                                crate::leanh::lean_dec(v_unused_3851_);
                                                v_unused_3852_ =
                                                    crate::leanh::lean_ctor_get(v_lchild_3801_, 0);
                                                crate::leanh::lean_dec(v_unused_3852_);
                                                v___x_3843_ = v_lchild_3801_;
                                                v_isShared_3844_ = v_isSharedCheck_3848_;
                                                state = 20;
                                                continue;
                                            } else {
                                                crate::leanh::lean_dec(v_lchild_3801_);
                                                v___x_3843_ = crate::leanh::lean_box(0);
                                                v_isShared_3844_ = v_isSharedCheck_3848_;
                                                state = 20;
                                                continue;
                                            }
                                        }
                                    }
                                } else {
                                    if crate::leanh::lean_obj_tag(v_rchild_3804_) == 1 {
                                        v_color_3853_ = crate::leanh::lean_ctor_get_uint8(
                                            v_rchild_3804_,
                                            (core::mem::size_of::<*mut crate::leanh::LeanObject>()
                                                * 4)
                                                as u32,
                                        );
                                        if v_color_3853_ == 0 {
                                            crate::leanh::lean_dec_ref_known(v___x_3799_, 4);
                                            v_lchild_3854_ =
                                                crate::leanh::lean_ctor_get(v_rchild_3804_, 0);
                                            crate::leanh::lean_inc(v_lchild_3854_);
                                            v_key_3855_ =
                                                crate::leanh::lean_ctor_get(v_rchild_3804_, 1);
                                            crate::leanh::lean_inc(v_key_3855_);
                                            v_val_3856_ =
                                                crate::leanh::lean_ctor_get(v_rchild_3804_, 2);
                                            crate::leanh::lean_inc(v_val_3856_);
                                            v_rchild_3857_ =
                                                crate::leanh::lean_ctor_get(v_rchild_3804_, 3);
                                            crate::leanh::lean_inc(v_rchild_3857_);
                                            crate::leanh::lean_dec_ref_known(v_rchild_3804_, 4);
                                            v_a_3806_ = v_lchild_3712_;
                                            v_kx_3807_ = v_key_3713_;
                                            v_vx_3808_ = v_val_3714_;
                                            v_b_3809_ = v_lchild_3801_;
                                            v_ky_3810_ = v_key_3802_;
                                            v_vy_3811_ = v_val_3803_;
                                            v_c_3812_ = v_lchild_3854_;
                                            v_kz_3813_ = v_key_3855_;
                                            v_vz_3814_ = v_val_3856_;
                                            v_d_3815_ = v_rchild_3857_;
                                            state = 16;
                                            continue;
                                        } else {
                                            crate::leanh::lean_dec(v_val_3803_);
                                            crate::leanh::lean_dec(v_key_3802_);
                                            crate::leanh::lean_dec(v_lchild_3801_);
                                            crate::leanh::lean_del_object(v___x_3717_);
                                            v_isSharedCheck_3864_ =
                                                (!crate::leanh::lean_is_exclusive(v_rchild_3804_))
                                                    as u8;
                                            if v_isSharedCheck_3864_ == 0 {
                                                v_unused_3865_ =
                                                    crate::leanh::lean_ctor_get(v_rchild_3804_, 3);
                                                crate::leanh::lean_dec(v_unused_3865_);
                                                v_unused_3866_ =
                                                    crate::leanh::lean_ctor_get(v_rchild_3804_, 2);
                                                crate::leanh::lean_dec(v_unused_3866_);
                                                v_unused_3867_ =
                                                    crate::leanh::lean_ctor_get(v_rchild_3804_, 1);
                                                crate::leanh::lean_dec(v_unused_3867_);
                                                v_unused_3868_ =
                                                    crate::leanh::lean_ctor_get(v_rchild_3804_, 0);
                                                crate::leanh::lean_dec(v_unused_3868_);
                                                v___x_3859_ = v_rchild_3804_;
                                                v_isShared_3860_ = v_isSharedCheck_3864_;
                                                state = 22;
                                                continue;
                                            } else {
                                                crate::leanh::lean_dec(v_rchild_3804_);
                                                v___x_3859_ = crate::leanh::lean_box(0);
                                                v_isShared_3860_ = v_isSharedCheck_3864_;
                                                state = 22;
                                                continue;
                                            }
                                        }
                                    } else {
                                        crate::leanh::lean_dec(v_rchild_3804_);
                                        crate::leanh::lean_dec(v_val_3803_);
                                        crate::leanh::lean_dec(v_key_3802_);
                                        crate::leanh::lean_dec(v_lchild_3801_);
                                        crate::leanh::lean_del_object(v___x_3717_);
                                        v___x_3869_ =
                                            crate::leanh::lean_alloc_ctor(1, 4, (1) as u32);
                                        crate::leanh::lean_ctor_set(v___x_3869_, 0, v_lchild_3712_);
                                        crate::leanh::lean_ctor_set(v___x_3869_, 1, v_key_3713_);
                                        crate::leanh::lean_ctor_set(v___x_3869_, 2, v_val_3714_);
                                        crate::leanh::lean_ctor_set(v___x_3869_, 3, v___x_3799_);
                                        crate::leanh::lean_ctor_set_uint8(
                                            v___x_3869_,
                                            (core::mem::size_of::<*mut crate::leanh::LeanObject>()
                                                * 4)
                                                as u32,
                                            v_color_3690_,
                                        );
                                        return v___x_3869_;
                                    }
                                }
                            } else {
                                crate::leanh::lean_dec(v_rchild_3804_);
                                crate::leanh::lean_dec(v_val_3803_);
                                crate::leanh::lean_dec(v_key_3802_);
                                crate::leanh::lean_dec(v_lchild_3801_);
                                crate::leanh::lean_del_object(v___x_3717_);
                                v___x_3870_ = crate::leanh::lean_alloc_ctor(1, 4, (1) as u32);
                                crate::leanh::lean_ctor_set(v___x_3870_, 0, v_lchild_3712_);
                                crate::leanh::lean_ctor_set(v___x_3870_, 1, v_key_3713_);
                                crate::leanh::lean_ctor_set(v___x_3870_, 2, v_val_3714_);
                                crate::leanh::lean_ctor_set(v___x_3870_, 3, v___x_3799_);
                                crate::leanh::lean_ctor_set_uint8(
                                    v___x_3870_,
                                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 4)
                                        as u32,
                                    v_color_3690_,
                                );
                                return v___x_3870_;
                            }
                        } else {
                            if v_isShared_3718_ == 0 {
                                crate::leanh::lean_ctor_set(v___x_3717_, 3, v___x_3799_);
                                v___x_3872_ = v___x_3717_;
                                state = 24;
                                continue;
                            } else {
                                v_reuseFailAlloc_3873_ =
                                    crate::leanh::lean_alloc_ctor(1, 4, (1) as u32);
                                crate::leanh::lean_ctor_set(
                                    v_reuseFailAlloc_3873_,
                                    0,
                                    v_lchild_3712_,
                                );
                                crate::leanh::lean_ctor_set(v_reuseFailAlloc_3873_, 1, v_key_3713_);
                                crate::leanh::lean_ctor_set(v_reuseFailAlloc_3873_, 2, v_val_3714_);
                                crate::leanh::lean_ctor_set(v_reuseFailAlloc_3873_, 3, v___x_3799_);
                                crate::leanh::lean_ctor_set_uint8(
                                    v_reuseFailAlloc_3873_,
                                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 4)
                                        as u32,
                                    v_color_3690_,
                                );
                                v___x_3872_ = v_reuseFailAlloc_3873_;
                                state = 24;
                                continue;
                            }
                        }
                    }
                }
            }
            6 => {
                if v_isShared_3718_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3717_, 3, v_b_3731_);
                    crate::leanh::lean_ctor_set(v___x_3717_, 2, v_vx_3730_);
                    crate::leanh::lean_ctor_set(v___x_3717_, 1, v_kx_3729_);
                    crate::leanh::lean_ctor_set(v___x_3717_, 0, v_a_3728_);
                    v___x_3739_ = v___x_3717_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_3742_ = crate::leanh::lean_alloc_ctor(1, 4, (1) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3742_, 0, v_a_3728_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3742_, 1, v_kx_3729_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3742_, 2, v_vx_3730_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3742_, 3, v_b_3731_);
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_3742_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 4) as u32,
                        v_color_3690_,
                    );
                    v___x_3739_ = v_reuseFailAlloc_3742_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                v___x_3740_ = crate::leanh::lean_alloc_ctor(1, 4, (1) as u32);
                crate::leanh::lean_ctor_set(v___x_3740_, 0, v_c_3734_);
                crate::leanh::lean_ctor_set(v___x_3740_, 1, v_kz_3735_);
                crate::leanh::lean_ctor_set(v___x_3740_, 2, v_vz_3736_);
                crate::leanh::lean_ctor_set(v___x_3740_, 3, v_d_3737_);
                crate::leanh::lean_ctor_set_uint8(
                    v___x_3740_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 4) as u32,
                    v_color_3690_,
                );
                v___x_3741_ = crate::leanh::lean_alloc_ctor(1, 4, (1) as u32);
                crate::leanh::lean_ctor_set(v___x_3741_, 0, v___x_3739_);
                crate::leanh::lean_ctor_set(v___x_3741_, 1, v_ky_3732_);
                crate::leanh::lean_ctor_set(v___x_3741_, 2, v_vy_3733_);
                crate::leanh::lean_ctor_set(v___x_3741_, 3, v___x_3740_);
                crate::leanh::lean_ctor_set_uint8(
                    v___x_3741_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 4) as u32,
                    v_color_3722_,
                );
                return v___x_3741_;
            }
            8 => {
                if v_isShared_3755_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3754_, 3, v_rchild_3715_);
                    crate::leanh::lean_ctor_set(v___x_3754_, 2, v_val_3714_);
                    crate::leanh::lean_ctor_set(v___x_3754_, 1, v_key_3713_);
                    crate::leanh::lean_ctor_set(v___x_3754_, 0, v___x_3721_);
                    v___x_3757_ = v___x_3754_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_3758_ = crate::leanh::lean_alloc_ctor(1, 4, (1) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3758_, 0, v___x_3721_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3758_, 1, v_key_3713_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3758_, 2, v_val_3714_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3758_, 3, v_rchild_3715_);
                    v___x_3757_ = v_reuseFailAlloc_3758_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                crate::leanh::lean_ctor_set_uint8(
                    v___x_3757_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 4) as u32,
                    v_color_3690_,
                );
                return v___x_3757_;
            }
            10 => {
                if v_isShared_3766_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3765_, 3, v_rchild_3715_);
                    crate::leanh::lean_ctor_set(v___x_3765_, 2, v_val_3714_);
                    crate::leanh::lean_ctor_set(v___x_3765_, 1, v_key_3713_);
                    crate::leanh::lean_ctor_set(v___x_3765_, 0, v___x_3721_);
                    v___x_3768_ = v___x_3765_;
                    state = 11;
                    continue;
                } else {
                    v_reuseFailAlloc_3769_ = crate::leanh::lean_alloc_ctor(1, 4, (1) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3769_, 0, v___x_3721_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3769_, 1, v_key_3713_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3769_, 2, v_val_3714_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3769_, 3, v_rchild_3715_);
                    v___x_3768_ = v_reuseFailAlloc_3769_;
                    state = 11;
                    continue;
                }
            }
            11 => {
                crate::leanh::lean_ctor_set_uint8(
                    v___x_3768_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 4) as u32,
                    v_color_3690_,
                );
                return v___x_3768_;
            }
            12 => {
                if v_isShared_3782_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3781_, 3, v_rchild_3715_);
                    crate::leanh::lean_ctor_set(v___x_3781_, 2, v_val_3714_);
                    crate::leanh::lean_ctor_set(v___x_3781_, 1, v_key_3713_);
                    crate::leanh::lean_ctor_set(v___x_3781_, 0, v___x_3721_);
                    v___x_3784_ = v___x_3781_;
                    state = 13;
                    continue;
                } else {
                    v_reuseFailAlloc_3785_ = crate::leanh::lean_alloc_ctor(1, 4, (1) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3785_, 0, v___x_3721_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3785_, 1, v_key_3713_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3785_, 2, v_val_3714_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3785_, 3, v_rchild_3715_);
                    v___x_3784_ = v_reuseFailAlloc_3785_;
                    state = 13;
                    continue;
                }
            }
            13 => {
                crate::leanh::lean_ctor_set_uint8(
                    v___x_3784_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 4) as u32,
                    v_color_3690_,
                );
                return v___x_3784_;
            }
            14 => {
                return v___x_3794_;
            }
            15 => {
                return v___x_3797_;
            }
            16 => {
                if v_isShared_3718_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3717_, 3, v_b_3809_);
                    crate::leanh::lean_ctor_set(v___x_3717_, 2, v_vx_3808_);
                    crate::leanh::lean_ctor_set(v___x_3717_, 1, v_kx_3807_);
                    crate::leanh::lean_ctor_set(v___x_3717_, 0, v_a_3806_);
                    v___x_3817_ = v___x_3717_;
                    state = 17;
                    continue;
                } else {
                    v_reuseFailAlloc_3820_ = crate::leanh::lean_alloc_ctor(1, 4, (1) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3820_, 0, v_a_3806_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3820_, 1, v_kx_3807_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3820_, 2, v_vx_3808_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3820_, 3, v_b_3809_);
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_3820_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 4) as u32,
                        v_color_3690_,
                    );
                    v___x_3817_ = v_reuseFailAlloc_3820_;
                    state = 17;
                    continue;
                }
            }
            17 => {
                v___x_3818_ = crate::leanh::lean_alloc_ctor(1, 4, (1) as u32);
                crate::leanh::lean_ctor_set(v___x_3818_, 0, v_c_3812_);
                crate::leanh::lean_ctor_set(v___x_3818_, 1, v_kz_3813_);
                crate::leanh::lean_ctor_set(v___x_3818_, 2, v_vz_3814_);
                crate::leanh::lean_ctor_set(v___x_3818_, 3, v_d_3815_);
                crate::leanh::lean_ctor_set_uint8(
                    v___x_3818_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 4) as u32,
                    v_color_3690_,
                );
                v___x_3819_ = crate::leanh::lean_alloc_ctor(1, 4, (1) as u32);
                crate::leanh::lean_ctor_set(v___x_3819_, 0, v___x_3817_);
                crate::leanh::lean_ctor_set(v___x_3819_, 1, v_ky_3810_);
                crate::leanh::lean_ctor_set(v___x_3819_, 2, v_vy_3811_);
                crate::leanh::lean_ctor_set(v___x_3819_, 3, v___x_3818_);
                crate::leanh::lean_ctor_set_uint8(
                    v___x_3819_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 4) as u32,
                    v_color_3800_,
                );
                return v___x_3819_;
            }
            18 => {
                if v_isShared_3833_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3832_, 3, v___x_3799_);
                    crate::leanh::lean_ctor_set(v___x_3832_, 2, v_val_3714_);
                    crate::leanh::lean_ctor_set(v___x_3832_, 1, v_key_3713_);
                    crate::leanh::lean_ctor_set(v___x_3832_, 0, v_lchild_3712_);
                    v___x_3835_ = v___x_3832_;
                    state = 19;
                    continue;
                } else {
                    v_reuseFailAlloc_3836_ = crate::leanh::lean_alloc_ctor(1, 4, (1) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3836_, 0, v_lchild_3712_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3836_, 1, v_key_3713_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3836_, 2, v_val_3714_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3836_, 3, v___x_3799_);
                    v___x_3835_ = v_reuseFailAlloc_3836_;
                    state = 19;
                    continue;
                }
            }
            19 => {
                crate::leanh::lean_ctor_set_uint8(
                    v___x_3835_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 4) as u32,
                    v_color_3690_,
                );
                return v___x_3835_;
            }
            20 => {
                if v_isShared_3844_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3843_, 3, v___x_3799_);
                    crate::leanh::lean_ctor_set(v___x_3843_, 2, v_val_3714_);
                    crate::leanh::lean_ctor_set(v___x_3843_, 1, v_key_3713_);
                    crate::leanh::lean_ctor_set(v___x_3843_, 0, v_lchild_3712_);
                    v___x_3846_ = v___x_3843_;
                    state = 21;
                    continue;
                } else {
                    v_reuseFailAlloc_3847_ = crate::leanh::lean_alloc_ctor(1, 4, (1) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3847_, 0, v_lchild_3712_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3847_, 1, v_key_3713_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3847_, 2, v_val_3714_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3847_, 3, v___x_3799_);
                    v___x_3846_ = v_reuseFailAlloc_3847_;
                    state = 21;
                    continue;
                }
            }
            21 => {
                crate::leanh::lean_ctor_set_uint8(
                    v___x_3846_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 4) as u32,
                    v_color_3690_,
                );
                return v___x_3846_;
            }
            22 => {
                if v_isShared_3860_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3859_, 3, v___x_3799_);
                    crate::leanh::lean_ctor_set(v___x_3859_, 2, v_val_3714_);
                    crate::leanh::lean_ctor_set(v___x_3859_, 1, v_key_3713_);
                    crate::leanh::lean_ctor_set(v___x_3859_, 0, v_lchild_3712_);
                    v___x_3862_ = v___x_3859_;
                    state = 23;
                    continue;
                } else {
                    v_reuseFailAlloc_3863_ = crate::leanh::lean_alloc_ctor(1, 4, (1) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3863_, 0, v_lchild_3712_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3863_, 1, v_key_3713_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3863_, 2, v_val_3714_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3863_, 3, v___x_3799_);
                    v___x_3862_ = v_reuseFailAlloc_3863_;
                    state = 23;
                    continue;
                }
            }
            23 => {
                crate::leanh::lean_ctor_set_uint8(
                    v___x_3862_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 4) as u32,
                    v_color_3690_,
                );
                return v___x_3862_;
            }
            24 => {
                return v___x_3872_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_RBNode_ins(
    mut v_00_u03b1_3875_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_3876_: *mut crate::leanh::LeanObject,
    mut v_cmp_3877_: *mut crate::leanh::LeanObject,
    mut v_x_3878_: *mut crate::leanh::LeanObject,
    mut v_x_3879_: *mut crate::leanh::LeanObject,
    mut v_x_3880_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3881_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3881_ = l_Lean_RBNode_ins___redArg(v_cmp_3877_, v_x_3878_, v_x_3879_, v_x_3880_);
    return v___x_3881_;
}
pub unsafe fn l_Lean_RBNode_setBlack___redArg(
    mut v_x_3882_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_lchild_3883_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_key_3884_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_3885_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_rchild_3886_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3888_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3889_: u8 = 0;
    let mut v___x_3890_: u8 = 0;
    let mut v___x_3892_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3893_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3894_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_3882_) == 1 {
                    v_lchild_3883_ = crate::leanh::lean_ctor_get(v_x_3882_, 0);
                    v_key_3884_ = crate::leanh::lean_ctor_get(v_x_3882_, 1);
                    v_val_3885_ = crate::leanh::lean_ctor_get(v_x_3882_, 2);
                    v_rchild_3886_ = crate::leanh::lean_ctor_get(v_x_3882_, 3);
                    v_isSharedCheck_3894_ = (!crate::leanh::lean_is_exclusive(v_x_3882_)) as u8;
                    if v_isSharedCheck_3894_ == 0 {
                        v___x_3888_ = v_x_3882_;
                        v_isShared_3889_ = v_isSharedCheck_3894_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_rchild_3886_);
                        crate::leanh::lean_inc(v_val_3885_);
                        crate::leanh::lean_inc(v_key_3884_);
                        crate::leanh::lean_inc(v_lchild_3883_);
                        crate::leanh::lean_dec(v_x_3882_);
                        v___x_3888_ = crate::leanh::lean_box(0);
                        v_isShared_3889_ = v_isSharedCheck_3894_;
                        state = 1;
                        continue;
                    }
                } else {
                    return v_x_3882_;
                }
            }
            1 => {
                v___x_3890_ = 1;
                if v_isShared_3889_ == 0 {
                    v___x_3892_ = v___x_3888_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3893_ = crate::leanh::lean_alloc_ctor(1, 4, (1) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3893_, 0, v_lchild_3883_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3893_, 1, v_key_3884_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3893_, 2, v_val_3885_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3893_, 3, v_rchild_3886_);
                    v___x_3892_ = v_reuseFailAlloc_3893_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                crate::leanh::lean_ctor_set_uint8(
                    v___x_3892_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 4) as u32,
                    v___x_3890_,
                );
                return v___x_3892_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_RBNode_setBlack(
    mut v_00_u03b1_3895_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_3896_: *mut crate::leanh::LeanObject,
    mut v_x_3897_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3898_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3898_ = l_Lean_RBNode_setBlack___redArg(v_x_3897_);
    return v___x_3898_;
}
pub unsafe fn l_Lean_RBNode_insert___redArg(
    mut v_cmp_3899_: *mut crate::leanh::LeanObject,
    mut v_t_3900_: *mut crate::leanh::LeanObject,
    mut v_k_3901_: *mut crate::leanh::LeanObject,
    mut v_v_3902_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3903_: u8 = 0;
    v___x_3903_ = l_Lean_RBNode_isRed___redArg(v_t_3900_);
    if v___x_3903_ == 0 {
        let mut v___x_3904_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_3904_ = l_Lean_RBNode_ins___redArg(v_cmp_3899_, v_t_3900_, v_k_3901_, v_v_3902_);
        return v___x_3904_;
    } else {
        let mut v___x_3905_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3906_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_3905_ = l_Lean_RBNode_ins___redArg(v_cmp_3899_, v_t_3900_, v_k_3901_, v_v_3902_);
        v___x_3906_ = l_Lean_RBNode_setBlack___redArg(v___x_3905_);
        return v___x_3906_;
    }
}
pub unsafe fn l_Lean_RBNode_insert(
    mut v_00_u03b1_3907_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_3908_: *mut crate::leanh::LeanObject,
    mut v_cmp_3909_: *mut crate::leanh::LeanObject,
    mut v_t_3910_: *mut crate::leanh::LeanObject,
    mut v_k_3911_: *mut crate::leanh::LeanObject,
    mut v_v_3912_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3913_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3913_ = l_Lean_RBNode_insert___redArg(v_cmp_3909_, v_t_3910_, v_k_3911_, v_v_3912_);
    return v___x_3913_;
}
pub unsafe fn l_Lean_RBNode_setRed___redArg(
    mut v_x_3914_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_lchild_3915_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_key_3916_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_3917_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_rchild_3918_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3920_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3921_: u8 = 0;
    let mut v___x_3922_: u8 = 0;
    let mut v___x_3924_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3925_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3926_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_3914_) == 1 {
                    v_lchild_3915_ = crate::leanh::lean_ctor_get(v_x_3914_, 0);
                    v_key_3916_ = crate::leanh::lean_ctor_get(v_x_3914_, 1);
                    v_val_3917_ = crate::leanh::lean_ctor_get(v_x_3914_, 2);
                    v_rchild_3918_ = crate::leanh::lean_ctor_get(v_x_3914_, 3);
                    v_isSharedCheck_3926_ = (!crate::leanh::lean_is_exclusive(v_x_3914_)) as u8;
                    if v_isSharedCheck_3926_ == 0 {
                        v___x_3920_ = v_x_3914_;
                        v_isShared_3921_ = v_isSharedCheck_3926_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_rchild_3918_);
                        crate::leanh::lean_inc(v_val_3917_);
                        crate::leanh::lean_inc(v_key_3916_);
                        crate::leanh::lean_inc(v_lchild_3915_);
                        crate::leanh::lean_dec(v_x_3914_);
                        v___x_3920_ = crate::leanh::lean_box(0);
                        v_isShared_3921_ = v_isSharedCheck_3926_;
                        state = 1;
                        continue;
                    }
                } else {
                    return v_x_3914_;
                }
            }
            1 => {
                v___x_3922_ = 0;
                if v_isShared_3921_ == 0 {
                    v___x_3924_ = v___x_3920_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3925_ = crate::leanh::lean_alloc_ctor(1, 4, (1) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3925_, 0, v_lchild_3915_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3925_, 1, v_key_3916_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3925_, 2, v_val_3917_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3925_, 3, v_rchild_3918_);
                    v___x_3924_ = v_reuseFailAlloc_3925_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                crate::leanh::lean_ctor_set_uint8(
                    v___x_3924_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 4) as u32,
                    v___x_3922_,
                );
                return v___x_3924_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_RBNode_setRed(
    mut v_00_u03b1_3927_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_3928_: *mut crate::leanh::LeanObject,
    mut v_x_3929_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3930_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3930_ = l_Lean_RBNode_setRed___redArg(v_x_3929_);
    return v___x_3930_;
}
pub unsafe fn l_Lean_RBNode_balLeft___redArg(
    mut v_x_3931_: *mut crate::leanh::LeanObject,
    mut v_x_3932_: *mut crate::leanh::LeanObject,
    mut v_x_3933_: *mut crate::leanh::LeanObject,
    mut v_x_3934_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_a_3936_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_kx_3937_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_vx_3938_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_b_3939_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3940_: u8 = 0;
    let mut v___x_3941_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3943_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_kx_3944_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_vx_3945_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_b_3946_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ky_3947_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_vy_3948_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_c_3949_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_kz_3950_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_vz_3951_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_d_3952_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3953_: u8 = 0;
    let mut v___x_3954_: u8 = 0;
    let mut v___x_3955_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3956_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3957_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_l_3959_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_3960_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_3961_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3962_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ky_3963_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_vy_3964_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_b_3965_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3966_: u8 = 0;
    let mut v___x_3967_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_color_3968_: u8 = 0;
    let mut v_lchild_3969_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_key_3970_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_3971_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_rchild_3972_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_color_3973_: u8 = 0;
    let mut v_lchild_3974_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_key_3975_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_3976_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_rchild_3977_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_color_3978_: u8 = 0;
    let mut v_lchild_3979_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_key_3980_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_3981_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_rchild_3982_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3984_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3985_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3986_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3987_: u8 = 0;
    let mut v___y_3988_: u8 = 0;
    let mut v_a_3989_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_kx_3990_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_vx_3991_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_b_3992_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ky_3993_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_vy_3994_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_c_3995_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_kz_3996_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_vz_3997_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_d_3998_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3999_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4000_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4001_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4002_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4004_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4005_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4006_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4007_: u8 = 0;
    let mut v___y_4008_: u8 = 0;
    let mut v_a_4009_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_kx_4010_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_vx_4011_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_b_4012_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4013_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4014_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_l_4016_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_4017_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_4018_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4019_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ky_4020_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_vy_4021_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_b_4022_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_kz_4023_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_vz_4024_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_c_4025_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4026_: u8 = 0;
    let mut v___x_4027_: u8 = 0;
    let mut v___x_4028_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4029_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_color_4030_: u8 = 0;
    let mut v_lchild_4031_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_color_4032_: u8 = 0;
    let mut v_key_4033_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_4034_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_rchild_4035_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_lchild_4036_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_key_4037_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_4038_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_rchild_4039_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_rchild_4040_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_color_4041_: u8 = 0;
    let mut v_key_4042_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_4043_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_lchild_4044_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_key_4045_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_4046_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_rchild_4047_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_rchild_4048_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_color_4049_: u8 = 0;
    let mut v_key_4050_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_4051_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_lchild_4052_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_key_4053_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_4054_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_rchild_4055_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_l_4057_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_4058_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_4059_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_4060_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4061_: u8 = 0;
    let mut v___x_4062_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_color_4063_: u8 = 0;
    let mut v_lchild_4064_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_key_4065_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_4066_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_rchild_4067_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4069_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4070_: u8 = 0;
    let mut v___x_4071_: u8 = 0;
    let mut v___x_4073_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4074_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4075_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4076_: u8 = 0;
    let mut v_color_4077_: u8 = 0;
    let mut v_lchild_4078_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_color_4079_: u8 = 0;
    let mut v_key_4080_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_4081_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_rchild_4082_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_lchild_4083_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_key_4084_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_4085_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_rchild_4086_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_lchild_4087_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_key_4088_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_4089_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_rchild_4090_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_color_4091_: u8 = 0;
    let mut v_lchild_4092_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_color_4093_: u8 = 0;
    let mut v_key_4094_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_4095_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_rchild_4096_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_lchild_4097_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_key_4098_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_4099_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_rchild_4100_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_lchild_4101_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_key_4102_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_4103_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_rchild_4104_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_3931_) == 1 {
                    v_color_4063_ = crate::leanh::lean_ctor_get_uint8(
                        v_x_3931_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 4) as u32,
                    );
                    if v_color_4063_ == 0 {
                        v_lchild_4064_ = crate::leanh::lean_ctor_get(v_x_3931_, 0);
                        v_key_4065_ = crate::leanh::lean_ctor_get(v_x_3931_, 1);
                        v_val_4066_ = crate::leanh::lean_ctor_get(v_x_3931_, 2);
                        v_rchild_4067_ = crate::leanh::lean_ctor_get(v_x_3931_, 3);
                        v_isSharedCheck_4076_ = (!crate::leanh::lean_is_exclusive(v_x_3931_)) as u8;
                        if v_isSharedCheck_4076_ == 0 {
                            v___x_4069_ = v_x_3931_;
                            v_isShared_4070_ = v_isSharedCheck_4076_;
                            state = 8;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_rchild_4067_);
                            crate::leanh::lean_inc(v_val_4066_);
                            crate::leanh::lean_inc(v_key_4065_);
                            crate::leanh::lean_inc(v_lchild_4064_);
                            crate::leanh::lean_dec(v_x_3931_);
                            v___x_4069_ = crate::leanh::lean_box(0);
                            v_isShared_4070_ = v_isSharedCheck_4076_;
                            state = 8;
                            continue;
                        }
                    } else {
                        if crate::leanh::lean_obj_tag(v_x_3934_) == 1 {
                            v_color_4077_ = crate::leanh::lean_ctor_get_uint8(
                                v_x_3934_,
                                (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 4) as u32,
                            );
                            if v_color_4077_ == 0 {
                                v_lchild_4078_ = crate::leanh::lean_ctor_get(v_x_3934_, 0);
                                if crate::leanh::lean_obj_tag(v_lchild_4078_) == 1 {
                                    v_color_4079_ = crate::leanh::lean_ctor_get_uint8(
                                        v_lchild_4078_,
                                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 4)
                                            as u32,
                                    );
                                    if v_color_4079_ == 1 {
                                        crate::leanh::lean_inc_ref(v_lchild_4078_);
                                        v_key_4080_ = crate::leanh::lean_ctor_get(v_x_3934_, 1);
                                        crate::leanh::lean_inc(v_key_4080_);
                                        v_val_4081_ = crate::leanh::lean_ctor_get(v_x_3934_, 2);
                                        crate::leanh::lean_inc(v_val_4081_);
                                        v_rchild_4082_ = crate::leanh::lean_ctor_get(v_x_3934_, 3);
                                        crate::leanh::lean_inc(v_rchild_4082_);
                                        crate::leanh::lean_dec_ref_known(v_x_3934_, 4);
                                        v_lchild_4083_ =
                                            crate::leanh::lean_ctor_get(v_lchild_4078_, 0);
                                        crate::leanh::lean_inc(v_lchild_4083_);
                                        v_key_4084_ =
                                            crate::leanh::lean_ctor_get(v_lchild_4078_, 1);
                                        crate::leanh::lean_inc(v_key_4084_);
                                        v_val_4085_ =
                                            crate::leanh::lean_ctor_get(v_lchild_4078_, 2);
                                        crate::leanh::lean_inc(v_val_4085_);
                                        v_rchild_4086_ =
                                            crate::leanh::lean_ctor_get(v_lchild_4078_, 3);
                                        crate::leanh::lean_inc(v_rchild_4086_);
                                        crate::leanh::lean_dec_ref_known(v_lchild_4078_, 4);
                                        v_l_4016_ = v_x_3931_;
                                        v_k_4017_ = v_x_3932_;
                                        v_v_4018_ = v_x_3933_;
                                        v_a_4019_ = v_lchild_4083_;
                                        v_ky_4020_ = v_key_4084_;
                                        v_vy_4021_ = v_val_4085_;
                                        v_b_4022_ = v_rchild_4086_;
                                        v_kz_4023_ = v_key_4080_;
                                        v_vz_4024_ = v_val_4081_;
                                        v_c_4025_ = v_rchild_4082_;
                                        state = 6;
                                        continue;
                                    } else {
                                        v_l_4057_ = v_x_3931_;
                                        v_k_4058_ = v_x_3932_;
                                        v_v_4059_ = v_x_3933_;
                                        v_r_4060_ = v_x_3934_;
                                        state = 7;
                                        continue;
                                    }
                                } else {
                                    v_l_4057_ = v_x_3931_;
                                    v_k_4058_ = v_x_3932_;
                                    v_v_4059_ = v_x_3933_;
                                    v_r_4060_ = v_x_3934_;
                                    state = 7;
                                    continue;
                                }
                            } else {
                                v_lchild_4087_ = crate::leanh::lean_ctor_get(v_x_3934_, 0);
                                crate::leanh::lean_inc(v_lchild_4087_);
                                v_key_4088_ = crate::leanh::lean_ctor_get(v_x_3934_, 1);
                                crate::leanh::lean_inc(v_key_4088_);
                                v_val_4089_ = crate::leanh::lean_ctor_get(v_x_3934_, 2);
                                crate::leanh::lean_inc(v_val_4089_);
                                v_rchild_4090_ = crate::leanh::lean_ctor_get(v_x_3934_, 3);
                                crate::leanh::lean_inc(v_rchild_4090_);
                                crate::leanh::lean_dec_ref_known(v_x_3934_, 4);
                                v_l_3959_ = v_x_3931_;
                                v_k_3960_ = v_x_3932_;
                                v_v_3961_ = v_x_3933_;
                                v_a_3962_ = v_lchild_4087_;
                                v_ky_3963_ = v_key_4088_;
                                v_vy_3964_ = v_val_4089_;
                                v_b_3965_ = v_rchild_4090_;
                                state = 3;
                                continue;
                            }
                        } else {
                            v_l_4057_ = v_x_3931_;
                            v_k_4058_ = v_x_3932_;
                            v_v_4059_ = v_x_3933_;
                            v_r_4060_ = v_x_3934_;
                            state = 7;
                            continue;
                        }
                    }
                } else {
                    if crate::leanh::lean_obj_tag(v_x_3934_) == 1 {
                        v_color_4091_ = crate::leanh::lean_ctor_get_uint8(
                            v_x_3934_,
                            (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 4) as u32,
                        );
                        if v_color_4091_ == 0 {
                            v_lchild_4092_ = crate::leanh::lean_ctor_get(v_x_3934_, 0);
                            if crate::leanh::lean_obj_tag(v_lchild_4092_) == 1 {
                                v_color_4093_ = crate::leanh::lean_ctor_get_uint8(
                                    v_lchild_4092_,
                                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 4)
                                        as u32,
                                );
                                if v_color_4093_ == 1 {
                                    crate::leanh::lean_inc_ref(v_lchild_4092_);
                                    v_key_4094_ = crate::leanh::lean_ctor_get(v_x_3934_, 1);
                                    crate::leanh::lean_inc(v_key_4094_);
                                    v_val_4095_ = crate::leanh::lean_ctor_get(v_x_3934_, 2);
                                    crate::leanh::lean_inc(v_val_4095_);
                                    v_rchild_4096_ = crate::leanh::lean_ctor_get(v_x_3934_, 3);
                                    crate::leanh::lean_inc(v_rchild_4096_);
                                    crate::leanh::lean_dec_ref_known(v_x_3934_, 4);
                                    v_lchild_4097_ = crate::leanh::lean_ctor_get(v_lchild_4092_, 0);
                                    crate::leanh::lean_inc(v_lchild_4097_);
                                    v_key_4098_ = crate::leanh::lean_ctor_get(v_lchild_4092_, 1);
                                    crate::leanh::lean_inc(v_key_4098_);
                                    v_val_4099_ = crate::leanh::lean_ctor_get(v_lchild_4092_, 2);
                                    crate::leanh::lean_inc(v_val_4099_);
                                    v_rchild_4100_ = crate::leanh::lean_ctor_get(v_lchild_4092_, 3);
                                    crate::leanh::lean_inc(v_rchild_4100_);
                                    crate::leanh::lean_dec_ref_known(v_lchild_4092_, 4);
                                    v_l_4016_ = v_x_3931_;
                                    v_k_4017_ = v_x_3932_;
                                    v_v_4018_ = v_x_3933_;
                                    v_a_4019_ = v_lchild_4097_;
                                    v_ky_4020_ = v_key_4098_;
                                    v_vy_4021_ = v_val_4099_;
                                    v_b_4022_ = v_rchild_4100_;
                                    v_kz_4023_ = v_key_4094_;
                                    v_vz_4024_ = v_val_4095_;
                                    v_c_4025_ = v_rchild_4096_;
                                    state = 6;
                                    continue;
                                } else {
                                    v_l_4057_ = v_x_3931_;
                                    v_k_4058_ = v_x_3932_;
                                    v_v_4059_ = v_x_3933_;
                                    v_r_4060_ = v_x_3934_;
                                    state = 7;
                                    continue;
                                }
                            } else {
                                v_l_4057_ = v_x_3931_;
                                v_k_4058_ = v_x_3932_;
                                v_v_4059_ = v_x_3933_;
                                v_r_4060_ = v_x_3934_;
                                state = 7;
                                continue;
                            }
                        } else {
                            v_lchild_4101_ = crate::leanh::lean_ctor_get(v_x_3934_, 0);
                            crate::leanh::lean_inc(v_lchild_4101_);
                            v_key_4102_ = crate::leanh::lean_ctor_get(v_x_3934_, 1);
                            crate::leanh::lean_inc(v_key_4102_);
                            v_val_4103_ = crate::leanh::lean_ctor_get(v_x_3934_, 2);
                            crate::leanh::lean_inc(v_val_4103_);
                            v_rchild_4104_ = crate::leanh::lean_ctor_get(v_x_3934_, 3);
                            crate::leanh::lean_inc(v_rchild_4104_);
                            crate::leanh::lean_dec_ref_known(v_x_3934_, 4);
                            v_l_3959_ = v_x_3931_;
                            v_k_3960_ = v_x_3932_;
                            v_v_3961_ = v_x_3933_;
                            v_a_3962_ = v_lchild_4101_;
                            v_ky_3963_ = v_key_4102_;
                            v_vy_3964_ = v_val_4103_;
                            v_b_3965_ = v_rchild_4104_;
                            state = 3;
                            continue;
                        }
                    } else {
                        v_l_4057_ = v_x_3931_;
                        v_k_4058_ = v_x_3932_;
                        v_v_4059_ = v_x_3933_;
                        v_r_4060_ = v_x_3934_;
                        state = 7;
                        continue;
                    }
                }
            }
            1 => {
                v___x_3940_ = 1;
                v___x_3941_ = crate::leanh::lean_alloc_ctor(1, 4, (1) as u32);
                crate::leanh::lean_ctor_set(v___x_3941_, 0, v_a_3936_);
                crate::leanh::lean_ctor_set(v___x_3941_, 1, v_kx_3937_);
                crate::leanh::lean_ctor_set(v___x_3941_, 2, v_vx_3938_);
                crate::leanh::lean_ctor_set(v___x_3941_, 3, v_b_3939_);
                crate::leanh::lean_ctor_set_uint8(
                    v___x_3941_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 4) as u32,
                    v___x_3940_,
                );
                return v___x_3941_;
            }
            2 => {
                v___x_3953_ = 0;
                v___x_3954_ = 1;
                v___x_3955_ = crate::leanh::lean_alloc_ctor(1, 4, (1) as u32);
                crate::leanh::lean_ctor_set(v___x_3955_, 0, v_a_3943_);
                crate::leanh::lean_ctor_set(v___x_3955_, 1, v_kx_3944_);
                crate::leanh::lean_ctor_set(v___x_3955_, 2, v_vx_3945_);
                crate::leanh::lean_ctor_set(v___x_3955_, 3, v_b_3946_);
                crate::leanh::lean_ctor_set_uint8(
                    v___x_3955_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 4) as u32,
                    v___x_3954_,
                );
                v___x_3956_ = crate::leanh::lean_alloc_ctor(1, 4, (1) as u32);
                crate::leanh::lean_ctor_set(v___x_3956_, 0, v_c_3949_);
                crate::leanh::lean_ctor_set(v___x_3956_, 1, v_kz_3950_);
                crate::leanh::lean_ctor_set(v___x_3956_, 2, v_vz_3951_);
                crate::leanh::lean_ctor_set(v___x_3956_, 3, v_d_3952_);
                crate::leanh::lean_ctor_set_uint8(
                    v___x_3956_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 4) as u32,
                    v___x_3954_,
                );
                v___x_3957_ = crate::leanh::lean_alloc_ctor(1, 4, (1) as u32);
                crate::leanh::lean_ctor_set(v___x_3957_, 0, v___x_3955_);
                crate::leanh::lean_ctor_set(v___x_3957_, 1, v_ky_3947_);
                crate::leanh::lean_ctor_set(v___x_3957_, 2, v_vy_3948_);
                crate::leanh::lean_ctor_set(v___x_3957_, 3, v___x_3956_);
                crate::leanh::lean_ctor_set_uint8(
                    v___x_3957_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 4) as u32,
                    v___x_3953_,
                );
                return v___x_3957_;
            }
            3 => {
                v___x_3966_ = 0;
                crate::leanh::lean_inc(v_b_3965_);
                crate::leanh::lean_inc(v_vy_3964_);
                crate::leanh::lean_inc(v_ky_3963_);
                crate::leanh::lean_inc(v_a_3962_);
                v___x_3967_ = crate::leanh::lean_alloc_ctor(1, 4, (1) as u32);
                crate::leanh::lean_ctor_set(v___x_3967_, 0, v_a_3962_);
                crate::leanh::lean_ctor_set(v___x_3967_, 1, v_ky_3963_);
                crate::leanh::lean_ctor_set(v___x_3967_, 2, v_vy_3964_);
                crate::leanh::lean_ctor_set(v___x_3967_, 3, v_b_3965_);
                crate::leanh::lean_ctor_set_uint8(
                    v___x_3967_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 4) as u32,
                    v___x_3966_,
                );
                if crate::leanh::lean_obj_tag(v_a_3962_) == 1 {
                    v_color_3968_ = crate::leanh::lean_ctor_get_uint8(
                        v_a_3962_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 4) as u32,
                    );
                    if v_color_3968_ == 0 {
                        crate::leanh::lean_dec_ref_known(v___x_3967_, 4);
                        v_lchild_3969_ = crate::leanh::lean_ctor_get(v_a_3962_, 0);
                        crate::leanh::lean_inc(v_lchild_3969_);
                        v_key_3970_ = crate::leanh::lean_ctor_get(v_a_3962_, 1);
                        crate::leanh::lean_inc(v_key_3970_);
                        v_val_3971_ = crate::leanh::lean_ctor_get(v_a_3962_, 2);
                        crate::leanh::lean_inc(v_val_3971_);
                        v_rchild_3972_ = crate::leanh::lean_ctor_get(v_a_3962_, 3);
                        crate::leanh::lean_inc(v_rchild_3972_);
                        crate::leanh::lean_dec_ref_known(v_a_3962_, 4);
                        v_a_3943_ = v_l_3959_;
                        v_kx_3944_ = v_k_3960_;
                        v_vx_3945_ = v_v_3961_;
                        v_b_3946_ = v_lchild_3969_;
                        v_ky_3947_ = v_key_3970_;
                        v_vy_3948_ = v_val_3971_;
                        v_c_3949_ = v_rchild_3972_;
                        v_kz_3950_ = v_ky_3963_;
                        v_vz_3951_ = v_vy_3964_;
                        v_d_3952_ = v_b_3965_;
                        state = 2;
                        continue;
                    } else {
                        if crate::leanh::lean_obj_tag(v_b_3965_) == 1 {
                            v_color_3973_ = crate::leanh::lean_ctor_get_uint8(
                                v_b_3965_,
                                (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 4) as u32,
                            );
                            if v_color_3973_ == 0 {
                                crate::leanh::lean_dec_ref_known(v___x_3967_, 4);
                                v_lchild_3974_ = crate::leanh::lean_ctor_get(v_b_3965_, 0);
                                crate::leanh::lean_inc(v_lchild_3974_);
                                v_key_3975_ = crate::leanh::lean_ctor_get(v_b_3965_, 1);
                                crate::leanh::lean_inc(v_key_3975_);
                                v_val_3976_ = crate::leanh::lean_ctor_get(v_b_3965_, 2);
                                crate::leanh::lean_inc(v_val_3976_);
                                v_rchild_3977_ = crate::leanh::lean_ctor_get(v_b_3965_, 3);
                                crate::leanh::lean_inc(v_rchild_3977_);
                                crate::leanh::lean_dec_ref_known(v_b_3965_, 4);
                                v_a_3943_ = v_l_3959_;
                                v_kx_3944_ = v_k_3960_;
                                v_vx_3945_ = v_v_3961_;
                                v_b_3946_ = v_a_3962_;
                                v_ky_3947_ = v_ky_3963_;
                                v_vy_3948_ = v_vy_3964_;
                                v_c_3949_ = v_lchild_3974_;
                                v_kz_3950_ = v_key_3975_;
                                v_vz_3951_ = v_val_3976_;
                                v_d_3952_ = v_rchild_3977_;
                                state = 2;
                                continue;
                            } else {
                                crate::leanh::lean_dec_ref_known(v_b_3965_, 4);
                                crate::leanh::lean_dec_ref_known(v_a_3962_, 4);
                                crate::leanh::lean_dec(v_vy_3964_);
                                crate::leanh::lean_dec(v_ky_3963_);
                                v_a_3936_ = v_l_3959_;
                                v_kx_3937_ = v_k_3960_;
                                v_vx_3938_ = v_v_3961_;
                                v_b_3939_ = v___x_3967_;
                                state = 1;
                                continue;
                            }
                        } else {
                            crate::leanh::lean_dec_ref_known(v_a_3962_, 4);
                            crate::leanh::lean_dec(v_b_3965_);
                            crate::leanh::lean_dec(v_vy_3964_);
                            crate::leanh::lean_dec(v_ky_3963_);
                            v_a_3936_ = v_l_3959_;
                            v_kx_3937_ = v_k_3960_;
                            v_vx_3938_ = v_v_3961_;
                            v_b_3939_ = v___x_3967_;
                            state = 1;
                            continue;
                        }
                    }
                } else {
                    if crate::leanh::lean_obj_tag(v_b_3965_) == 1 {
                        v_color_3978_ = crate::leanh::lean_ctor_get_uint8(
                            v_b_3965_,
                            (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 4) as u32,
                        );
                        if v_color_3978_ == 0 {
                            crate::leanh::lean_dec_ref_known(v___x_3967_, 4);
                            v_lchild_3979_ = crate::leanh::lean_ctor_get(v_b_3965_, 0);
                            crate::leanh::lean_inc(v_lchild_3979_);
                            v_key_3980_ = crate::leanh::lean_ctor_get(v_b_3965_, 1);
                            crate::leanh::lean_inc(v_key_3980_);
                            v_val_3981_ = crate::leanh::lean_ctor_get(v_b_3965_, 2);
                            crate::leanh::lean_inc(v_val_3981_);
                            v_rchild_3982_ = crate::leanh::lean_ctor_get(v_b_3965_, 3);
                            crate::leanh::lean_inc(v_rchild_3982_);
                            crate::leanh::lean_dec_ref_known(v_b_3965_, 4);
                            v_a_3943_ = v_l_3959_;
                            v_kx_3944_ = v_k_3960_;
                            v_vx_3945_ = v_v_3961_;
                            v_b_3946_ = v_a_3962_;
                            v_ky_3947_ = v_ky_3963_;
                            v_vy_3948_ = v_vy_3964_;
                            v_c_3949_ = v_lchild_3979_;
                            v_kz_3950_ = v_key_3980_;
                            v_vz_3951_ = v_val_3981_;
                            v_d_3952_ = v_rchild_3982_;
                            state = 2;
                            continue;
                        } else {
                            crate::leanh::lean_dec_ref_known(v_b_3965_, 4);
                            crate::leanh::lean_dec(v_vy_3964_);
                            crate::leanh::lean_dec(v_ky_3963_);
                            crate::leanh::lean_dec(v_a_3962_);
                            v_a_3936_ = v_l_3959_;
                            v_kx_3937_ = v_k_3960_;
                            v_vx_3938_ = v_v_3961_;
                            v_b_3939_ = v___x_3967_;
                            state = 1;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec(v_b_3965_);
                        crate::leanh::lean_dec(v_vy_3964_);
                        crate::leanh::lean_dec(v_ky_3963_);
                        crate::leanh::lean_dec(v_a_3962_);
                        v_a_3936_ = v_l_3959_;
                        v_kx_3937_ = v_k_3960_;
                        v_vx_3938_ = v_v_3961_;
                        v_b_3939_ = v___x_3967_;
                        state = 1;
                        continue;
                    }
                }
            }
            4 => {
                v___x_3999_ = crate::leanh::lean_alloc_ctor(1, 4, (1) as u32);
                crate::leanh::lean_ctor_set(v___x_3999_, 0, v_a_3989_);
                crate::leanh::lean_ctor_set(v___x_3999_, 1, v_kx_3990_);
                crate::leanh::lean_ctor_set(v___x_3999_, 2, v_vx_3991_);
                crate::leanh::lean_ctor_set(v___x_3999_, 3, v_b_3992_);
                crate::leanh::lean_ctor_set_uint8(
                    v___x_3999_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 4) as u32,
                    v___y_3988_,
                );
                v___x_4000_ = crate::leanh::lean_alloc_ctor(1, 4, (1) as u32);
                crate::leanh::lean_ctor_set(v___x_4000_, 0, v_c_3995_);
                crate::leanh::lean_ctor_set(v___x_4000_, 1, v_kz_3996_);
                crate::leanh::lean_ctor_set(v___x_4000_, 2, v_vz_3997_);
                crate::leanh::lean_ctor_set(v___x_4000_, 3, v_d_3998_);
                crate::leanh::lean_ctor_set_uint8(
                    v___x_4000_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 4) as u32,
                    v___y_3988_,
                );
                v___x_4001_ = crate::leanh::lean_alloc_ctor(1, 4, (1) as u32);
                crate::leanh::lean_ctor_set(v___x_4001_, 0, v___x_3999_);
                crate::leanh::lean_ctor_set(v___x_4001_, 1, v_ky_3993_);
                crate::leanh::lean_ctor_set(v___x_4001_, 2, v_vy_3994_);
                crate::leanh::lean_ctor_set(v___x_4001_, 3, v___x_4000_);
                crate::leanh::lean_ctor_set_uint8(
                    v___x_4001_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 4) as u32,
                    v___y_3987_,
                );
                v___x_4002_ = crate::leanh::lean_alloc_ctor(1, 4, (1) as u32);
                crate::leanh::lean_ctor_set(v___x_4002_, 0, v___y_3985_);
                crate::leanh::lean_ctor_set(v___x_4002_, 1, v___y_3984_);
                crate::leanh::lean_ctor_set(v___x_4002_, 2, v___y_3986_);
                crate::leanh::lean_ctor_set(v___x_4002_, 3, v___x_4001_);
                crate::leanh::lean_ctor_set_uint8(
                    v___x_4002_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 4) as u32,
                    v___y_3987_,
                );
                return v___x_4002_;
            }
            5 => {
                v___x_4013_ = crate::leanh::lean_alloc_ctor(1, 4, (1) as u32);
                crate::leanh::lean_ctor_set(v___x_4013_, 0, v_a_4009_);
                crate::leanh::lean_ctor_set(v___x_4013_, 1, v_kx_4010_);
                crate::leanh::lean_ctor_set(v___x_4013_, 2, v_vx_4011_);
                crate::leanh::lean_ctor_set(v___x_4013_, 3, v_b_4012_);
                crate::leanh::lean_ctor_set_uint8(
                    v___x_4013_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 4) as u32,
                    v___y_4008_,
                );
                v___x_4014_ = crate::leanh::lean_alloc_ctor(1, 4, (1) as u32);
                crate::leanh::lean_ctor_set(v___x_4014_, 0, v___y_4005_);
                crate::leanh::lean_ctor_set(v___x_4014_, 1, v___y_4004_);
                crate::leanh::lean_ctor_set(v___x_4014_, 2, v___y_4006_);
                crate::leanh::lean_ctor_set(v___x_4014_, 3, v___x_4013_);
                crate::leanh::lean_ctor_set_uint8(
                    v___x_4014_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 4) as u32,
                    v___y_4007_,
                );
                return v___x_4014_;
            }
            6 => {
                v___x_4026_ = 0;
                v___x_4027_ = 1;
                v___x_4028_ = crate::leanh::lean_alloc_ctor(1, 4, (1) as u32);
                crate::leanh::lean_ctor_set(v___x_4028_, 0, v_l_4016_);
                crate::leanh::lean_ctor_set(v___x_4028_, 1, v_k_4017_);
                crate::leanh::lean_ctor_set(v___x_4028_, 2, v_v_4018_);
                crate::leanh::lean_ctor_set(v___x_4028_, 3, v_a_4019_);
                crate::leanh::lean_ctor_set_uint8(
                    v___x_4028_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 4) as u32,
                    v___x_4027_,
                );
                v___x_4029_ = l_Lean_RBNode_setRed___redArg(v_c_4025_);
                if crate::leanh::lean_obj_tag(v___x_4029_) == 1 {
                    v_color_4030_ = crate::leanh::lean_ctor_get_uint8(
                        v___x_4029_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 4) as u32,
                    );
                    if v_color_4030_ == 0 {
                        v_lchild_4031_ = crate::leanh::lean_ctor_get(v___x_4029_, 0);
                        crate::leanh::lean_inc(v_lchild_4031_);
                        if crate::leanh::lean_obj_tag(v_lchild_4031_) == 1 {
                            v_color_4032_ = crate::leanh::lean_ctor_get_uint8(
                                v_lchild_4031_,
                                (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 4) as u32,
                            );
                            if v_color_4032_ == 0 {
                                v_key_4033_ = crate::leanh::lean_ctor_get(v___x_4029_, 1);
                                crate::leanh::lean_inc(v_key_4033_);
                                v_val_4034_ = crate::leanh::lean_ctor_get(v___x_4029_, 2);
                                crate::leanh::lean_inc(v_val_4034_);
                                v_rchild_4035_ = crate::leanh::lean_ctor_get(v___x_4029_, 3);
                                crate::leanh::lean_inc(v_rchild_4035_);
                                crate::leanh::lean_dec_ref_known(v___x_4029_, 4);
                                v_lchild_4036_ = crate::leanh::lean_ctor_get(v_lchild_4031_, 0);
                                crate::leanh::lean_inc(v_lchild_4036_);
                                v_key_4037_ = crate::leanh::lean_ctor_get(v_lchild_4031_, 1);
                                crate::leanh::lean_inc(v_key_4037_);
                                v_val_4038_ = crate::leanh::lean_ctor_get(v_lchild_4031_, 2);
                                crate::leanh::lean_inc(v_val_4038_);
                                v_rchild_4039_ = crate::leanh::lean_ctor_get(v_lchild_4031_, 3);
                                crate::leanh::lean_inc(v_rchild_4039_);
                                crate::leanh::lean_dec_ref_known(v_lchild_4031_, 4);
                                v___y_3984_ = v_ky_4020_;
                                v___y_3985_ = v___x_4028_;
                                v___y_3986_ = v_vy_4021_;
                                v___y_3987_ = v___x_4026_;
                                v___y_3988_ = v___x_4027_;
                                v_a_3989_ = v_b_4022_;
                                v_kx_3990_ = v_kz_4023_;
                                v_vx_3991_ = v_vz_4024_;
                                v_b_3992_ = v_lchild_4036_;
                                v_ky_3993_ = v_key_4037_;
                                v_vy_3994_ = v_val_4038_;
                                v_c_3995_ = v_rchild_4039_;
                                v_kz_3996_ = v_key_4033_;
                                v_vz_3997_ = v_val_4034_;
                                v_d_3998_ = v_rchild_4035_;
                                state = 4;
                                continue;
                            } else {
                                v_rchild_4040_ = crate::leanh::lean_ctor_get(v___x_4029_, 3);
                                crate::leanh::lean_inc(v_rchild_4040_);
                                if crate::leanh::lean_obj_tag(v_rchild_4040_) == 1 {
                                    v_color_4041_ = crate::leanh::lean_ctor_get_uint8(
                                        v_rchild_4040_,
                                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 4)
                                            as u32,
                                    );
                                    if v_color_4041_ == 0 {
                                        v_key_4042_ = crate::leanh::lean_ctor_get(v___x_4029_, 1);
                                        crate::leanh::lean_inc(v_key_4042_);
                                        v_val_4043_ = crate::leanh::lean_ctor_get(v___x_4029_, 2);
                                        crate::leanh::lean_inc(v_val_4043_);
                                        crate::leanh::lean_dec_ref_known(v___x_4029_, 4);
                                        v_lchild_4044_ =
                                            crate::leanh::lean_ctor_get(v_rchild_4040_, 0);
                                        crate::leanh::lean_inc(v_lchild_4044_);
                                        v_key_4045_ =
                                            crate::leanh::lean_ctor_get(v_rchild_4040_, 1);
                                        crate::leanh::lean_inc(v_key_4045_);
                                        v_val_4046_ =
                                            crate::leanh::lean_ctor_get(v_rchild_4040_, 2);
                                        crate::leanh::lean_inc(v_val_4046_);
                                        v_rchild_4047_ =
                                            crate::leanh::lean_ctor_get(v_rchild_4040_, 3);
                                        crate::leanh::lean_inc(v_rchild_4047_);
                                        crate::leanh::lean_dec_ref_known(v_rchild_4040_, 4);
                                        v___y_3984_ = v_ky_4020_;
                                        v___y_3985_ = v___x_4028_;
                                        v___y_3986_ = v_vy_4021_;
                                        v___y_3987_ = v___x_4026_;
                                        v___y_3988_ = v___x_4027_;
                                        v_a_3989_ = v_b_4022_;
                                        v_kx_3990_ = v_kz_4023_;
                                        v_vx_3991_ = v_vz_4024_;
                                        v_b_3992_ = v_lchild_4031_;
                                        v_ky_3993_ = v_key_4042_;
                                        v_vy_3994_ = v_val_4043_;
                                        v_c_3995_ = v_lchild_4044_;
                                        v_kz_3996_ = v_key_4045_;
                                        v_vz_3997_ = v_val_4046_;
                                        v_d_3998_ = v_rchild_4047_;
                                        state = 4;
                                        continue;
                                    } else {
                                        crate::leanh::lean_dec_ref_known(v_rchild_4040_, 4);
                                        crate::leanh::lean_dec_ref_known(v_lchild_4031_, 4);
                                        v___y_4004_ = v_ky_4020_;
                                        v___y_4005_ = v___x_4028_;
                                        v___y_4006_ = v_vy_4021_;
                                        v___y_4007_ = v___x_4026_;
                                        v___y_4008_ = v___x_4027_;
                                        v_a_4009_ = v_b_4022_;
                                        v_kx_4010_ = v_kz_4023_;
                                        v_vx_4011_ = v_vz_4024_;
                                        v_b_4012_ = v___x_4029_;
                                        state = 5;
                                        continue;
                                    }
                                } else {
                                    crate::leanh::lean_dec(v_rchild_4040_);
                                    crate::leanh::lean_dec_ref_known(v_lchild_4031_, 4);
                                    v___y_4004_ = v_ky_4020_;
                                    v___y_4005_ = v___x_4028_;
                                    v___y_4006_ = v_vy_4021_;
                                    v___y_4007_ = v___x_4026_;
                                    v___y_4008_ = v___x_4027_;
                                    v_a_4009_ = v_b_4022_;
                                    v_kx_4010_ = v_kz_4023_;
                                    v_vx_4011_ = v_vz_4024_;
                                    v_b_4012_ = v___x_4029_;
                                    state = 5;
                                    continue;
                                }
                            }
                        } else {
                            v_rchild_4048_ = crate::leanh::lean_ctor_get(v___x_4029_, 3);
                            crate::leanh::lean_inc(v_rchild_4048_);
                            if crate::leanh::lean_obj_tag(v_rchild_4048_) == 1 {
                                v_color_4049_ = crate::leanh::lean_ctor_get_uint8(
                                    v_rchild_4048_,
                                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 4)
                                        as u32,
                                );
                                if v_color_4049_ == 0 {
                                    v_key_4050_ = crate::leanh::lean_ctor_get(v___x_4029_, 1);
                                    crate::leanh::lean_inc(v_key_4050_);
                                    v_val_4051_ = crate::leanh::lean_ctor_get(v___x_4029_, 2);
                                    crate::leanh::lean_inc(v_val_4051_);
                                    crate::leanh::lean_dec_ref_known(v___x_4029_, 4);
                                    v_lchild_4052_ = crate::leanh::lean_ctor_get(v_rchild_4048_, 0);
                                    crate::leanh::lean_inc(v_lchild_4052_);
                                    v_key_4053_ = crate::leanh::lean_ctor_get(v_rchild_4048_, 1);
                                    crate::leanh::lean_inc(v_key_4053_);
                                    v_val_4054_ = crate::leanh::lean_ctor_get(v_rchild_4048_, 2);
                                    crate::leanh::lean_inc(v_val_4054_);
                                    v_rchild_4055_ = crate::leanh::lean_ctor_get(v_rchild_4048_, 3);
                                    crate::leanh::lean_inc(v_rchild_4055_);
                                    crate::leanh::lean_dec_ref_known(v_rchild_4048_, 4);
                                    v___y_3984_ = v_ky_4020_;
                                    v___y_3985_ = v___x_4028_;
                                    v___y_3986_ = v_vy_4021_;
                                    v___y_3987_ = v___x_4026_;
                                    v___y_3988_ = v___x_4027_;
                                    v_a_3989_ = v_b_4022_;
                                    v_kx_3990_ = v_kz_4023_;
                                    v_vx_3991_ = v_vz_4024_;
                                    v_b_3992_ = v_lchild_4031_;
                                    v_ky_3993_ = v_key_4050_;
                                    v_vy_3994_ = v_val_4051_;
                                    v_c_3995_ = v_lchild_4052_;
                                    v_kz_3996_ = v_key_4053_;
                                    v_vz_3997_ = v_val_4054_;
                                    v_d_3998_ = v_rchild_4055_;
                                    state = 4;
                                    continue;
                                } else {
                                    crate::leanh::lean_dec_ref_known(v_rchild_4048_, 4);
                                    crate::leanh::lean_dec(v_lchild_4031_);
                                    v___y_4004_ = v_ky_4020_;
                                    v___y_4005_ = v___x_4028_;
                                    v___y_4006_ = v_vy_4021_;
                                    v___y_4007_ = v___x_4026_;
                                    v___y_4008_ = v___x_4027_;
                                    v_a_4009_ = v_b_4022_;
                                    v_kx_4010_ = v_kz_4023_;
                                    v_vx_4011_ = v_vz_4024_;
                                    v_b_4012_ = v___x_4029_;
                                    state = 5;
                                    continue;
                                }
                            } else {
                                crate::leanh::lean_dec(v_rchild_4048_);
                                crate::leanh::lean_dec(v_lchild_4031_);
                                v___y_4004_ = v_ky_4020_;
                                v___y_4005_ = v___x_4028_;
                                v___y_4006_ = v_vy_4021_;
                                v___y_4007_ = v___x_4026_;
                                v___y_4008_ = v___x_4027_;
                                v_a_4009_ = v_b_4022_;
                                v_kx_4010_ = v_kz_4023_;
                                v_vx_4011_ = v_vz_4024_;
                                v_b_4012_ = v___x_4029_;
                                state = 5;
                                continue;
                            }
                        }
                    } else {
                        v___y_4004_ = v_ky_4020_;
                        v___y_4005_ = v___x_4028_;
                        v___y_4006_ = v_vy_4021_;
                        v___y_4007_ = v___x_4026_;
                        v___y_4008_ = v___x_4027_;
                        v_a_4009_ = v_b_4022_;
                        v_kx_4010_ = v_kz_4023_;
                        v_vx_4011_ = v_vz_4024_;
                        v_b_4012_ = v___x_4029_;
                        state = 5;
                        continue;
                    }
                } else {
                    v___y_4004_ = v_ky_4020_;
                    v___y_4005_ = v___x_4028_;
                    v___y_4006_ = v_vy_4021_;
                    v___y_4007_ = v___x_4026_;
                    v___y_4008_ = v___x_4027_;
                    v_a_4009_ = v_b_4022_;
                    v_kx_4010_ = v_kz_4023_;
                    v_vx_4011_ = v_vz_4024_;
                    v_b_4012_ = v___x_4029_;
                    state = 5;
                    continue;
                }
            }
            7 => {
                v___x_4061_ = 0;
                v___x_4062_ = crate::leanh::lean_alloc_ctor(1, 4, (1) as u32);
                crate::leanh::lean_ctor_set(v___x_4062_, 0, v_l_4057_);
                crate::leanh::lean_ctor_set(v___x_4062_, 1, v_k_4058_);
                crate::leanh::lean_ctor_set(v___x_4062_, 2, v_v_4059_);
                crate::leanh::lean_ctor_set(v___x_4062_, 3, v_r_4060_);
                crate::leanh::lean_ctor_set_uint8(
                    v___x_4062_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 4) as u32,
                    v___x_4061_,
                );
                return v___x_4062_;
            }
            8 => {
                v___x_4071_ = 1;
                if v_isShared_4070_ == 0 {
                    v___x_4073_ = v___x_4069_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_4075_ = crate::leanh::lean_alloc_ctor(1, 4, (1) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4075_, 0, v_lchild_4064_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4075_, 1, v_key_4065_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4075_, 2, v_val_4066_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4075_, 3, v_rchild_4067_);
                    v___x_4073_ = v_reuseFailAlloc_4075_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                crate::leanh::lean_ctor_set_uint8(
                    v___x_4073_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 4) as u32,
                    v___x_4071_,
                );
                v___x_4074_ = crate::leanh::lean_alloc_ctor(1, 4, (1) as u32);
                crate::leanh::lean_ctor_set(v___x_4074_, 0, v___x_4073_);
                crate::leanh::lean_ctor_set(v___x_4074_, 1, v_x_3932_);
                crate::leanh::lean_ctor_set(v___x_4074_, 2, v_x_3933_);
                crate::leanh::lean_ctor_set(v___x_4074_, 3, v_x_3934_);
                crate::leanh::lean_ctor_set_uint8(
                    v___x_4074_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 4) as u32,
                    v_color_4063_,
                );
                return v___x_4074_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_RBNode_balLeft(
    mut v_00_u03b1_4105_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_4106_: *mut crate::leanh::LeanObject,
    mut v_x_4107_: *mut crate::leanh::LeanObject,
    mut v_x_4108_: *mut crate::leanh::LeanObject,
    mut v_x_4109_: *mut crate::leanh::LeanObject,
    mut v_x_4110_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4111_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4111_ = l_Lean_RBNode_balLeft___redArg(v_x_4107_, v_x_4108_, v_x_4109_, v_x_4110_);
    return v___x_4111_;
}
pub unsafe fn l_Lean_RBNode_balRight___redArg(
    mut v_l_4112_: *mut crate::leanh::LeanObject,
    mut v_k_4113_: *mut crate::leanh::LeanObject,
    mut v_v_4114_: *mut crate::leanh::LeanObject,
    mut v_r_4115_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4117_: u8 = 0;
    let mut v___x_4118_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4120_: u8 = 0;
    let mut v_a_4121_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_kx_4122_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_vx_4123_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_b_4124_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ky_4125_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_vy_4126_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_c_4127_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_kz_4128_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_vz_4129_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_d_4130_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4131_: u8 = 0;
    let mut v___x_4132_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4133_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4134_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4136_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4137_: u8 = 0;
    let mut v___y_4138_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4139_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4140_: u8 = 0;
    let mut v___y_4141_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4142_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4143_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4145_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4146_: u8 = 0;
    let mut v___y_4147_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4148_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4149_: u8 = 0;
    let mut v_a_4150_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_kx_4151_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_vx_4152_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_b_4153_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ky_4154_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_vy_4155_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_c_4156_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_kz_4157_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_vz_4158_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_d_4159_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4160_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4161_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4162_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4164_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4165_: u8 = 0;
    let mut v___y_4166_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4167_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4168_: u8 = 0;
    let mut v_a_4169_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_kx_4170_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_vx_4171_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_b_4172_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4173_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_color_4175_: u8 = 0;
    let mut v_rchild_4176_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_color_4177_: u8 = 0;
    let mut v_lchild_4178_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_key_4179_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_4180_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_lchild_4181_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_key_4182_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_4183_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_rchild_4184_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4185_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_color_4186_: u8 = 0;
    let mut v_lchild_4187_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_color_4188_: u8 = 0;
    let mut v_key_4189_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_4190_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_rchild_4191_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_lchild_4192_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_key_4193_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_4194_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_rchild_4195_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_rchild_4196_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_color_4197_: u8 = 0;
    let mut v_key_4198_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_4199_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_lchild_4200_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_key_4201_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_4202_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_rchild_4203_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_rchild_4204_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_color_4205_: u8 = 0;
    let mut v_key_4206_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_4207_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_lchild_4208_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_key_4209_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_4210_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_rchild_4211_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_lchild_4212_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_key_4213_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_4214_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_rchild_4215_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4217_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4218_: u8 = 0;
    let mut v___x_4219_: u8 = 0;
    let mut v___x_4221_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_color_4222_: u8 = 0;
    let mut v_lchild_4223_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_key_4224_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_4225_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_rchild_4226_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_color_4227_: u8 = 0;
    let mut v_lchild_4228_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_key_4229_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_4230_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_rchild_4231_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4233_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4234_: u8 = 0;
    let mut v___x_4236_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4237_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4238_: u8 = 0;
    let mut v_unused_4239_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_4240_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_4241_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_4242_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4244_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4245_: u8 = 0;
    let mut v___x_4247_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4248_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4249_: u8 = 0;
    let mut v_unused_4250_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_4251_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_4252_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_4253_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_color_4254_: u8 = 0;
    let mut v_lchild_4255_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_key_4256_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_4257_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_rchild_4258_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4260_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4261_: u8 = 0;
    let mut v___x_4263_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4264_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4265_: u8 = 0;
    let mut v_unused_4266_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_4267_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_4268_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_4269_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4270_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4271_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4272_: u8 = 0;
    let mut v_color_4273_: u8 = 0;
    let mut v_lchild_4274_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_key_4275_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_4276_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_rchild_4277_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4279_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4280_: u8 = 0;
    let mut v___x_4281_: u8 = 0;
    let mut v___x_4283_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4284_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4285_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4286_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_r_4115_) == 1 {
                    v_color_4273_ = crate::leanh::lean_ctor_get_uint8(
                        v_r_4115_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 4) as u32,
                    );
                    if v_color_4273_ == 0 {
                        v_lchild_4274_ = crate::leanh::lean_ctor_get(v_r_4115_, 0);
                        v_key_4275_ = crate::leanh::lean_ctor_get(v_r_4115_, 1);
                        v_val_4276_ = crate::leanh::lean_ctor_get(v_r_4115_, 2);
                        v_rchild_4277_ = crate::leanh::lean_ctor_get(v_r_4115_, 3);
                        v_isSharedCheck_4286_ = (!crate::leanh::lean_is_exclusive(v_r_4115_)) as u8;
                        if v_isSharedCheck_4286_ == 0 {
                            v___x_4279_ = v_r_4115_;
                            v_isShared_4280_ = v_isSharedCheck_4286_;
                            state = 15;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_rchild_4277_);
                            crate::leanh::lean_inc(v_val_4276_);
                            crate::leanh::lean_inc(v_key_4275_);
                            crate::leanh::lean_inc(v_lchild_4274_);
                            crate::leanh::lean_dec(v_r_4115_);
                            v___x_4279_ = crate::leanh::lean_box(0);
                            v_isShared_4280_ = v_isSharedCheck_4286_;
                            state = 15;
                            continue;
                        }
                    } else {
                        state = 6;
                        continue;
                    }
                } else {
                    state = 6;
                    continue;
                }
            }
            1 => {
                v___x_4117_ = 0;
                v___x_4118_ = crate::leanh::lean_alloc_ctor(1, 4, (1) as u32);
                crate::leanh::lean_ctor_set(v___x_4118_, 0, v_l_4112_);
                crate::leanh::lean_ctor_set(v___x_4118_, 1, v_k_4113_);
                crate::leanh::lean_ctor_set(v___x_4118_, 2, v_v_4114_);
                crate::leanh::lean_ctor_set(v___x_4118_, 3, v_r_4115_);
                crate::leanh::lean_ctor_set_uint8(
                    v___x_4118_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 4) as u32,
                    v___x_4117_,
                );
                return v___x_4118_;
            }
            2 => {
                v___x_4131_ = 0;
                v___x_4132_ = crate::leanh::lean_alloc_ctor(1, 4, (1) as u32);
                crate::leanh::lean_ctor_set(v___x_4132_, 0, v_a_4121_);
                crate::leanh::lean_ctor_set(v___x_4132_, 1, v_kx_4122_);
                crate::leanh::lean_ctor_set(v___x_4132_, 2, v_vx_4123_);
                crate::leanh::lean_ctor_set(v___x_4132_, 3, v_b_4124_);
                crate::leanh::lean_ctor_set_uint8(
                    v___x_4132_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 4) as u32,
                    v___y_4120_,
                );
                v___x_4133_ = crate::leanh::lean_alloc_ctor(1, 4, (1) as u32);
                crate::leanh::lean_ctor_set(v___x_4133_, 0, v_c_4127_);
                crate::leanh::lean_ctor_set(v___x_4133_, 1, v_kz_4128_);
                crate::leanh::lean_ctor_set(v___x_4133_, 2, v_vz_4129_);
                crate::leanh::lean_ctor_set(v___x_4133_, 3, v_d_4130_);
                crate::leanh::lean_ctor_set_uint8(
                    v___x_4133_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 4) as u32,
                    v___y_4120_,
                );
                v___x_4134_ = crate::leanh::lean_alloc_ctor(1, 4, (1) as u32);
                crate::leanh::lean_ctor_set(v___x_4134_, 0, v___x_4132_);
                crate::leanh::lean_ctor_set(v___x_4134_, 1, v_ky_4125_);
                crate::leanh::lean_ctor_set(v___x_4134_, 2, v_vy_4126_);
                crate::leanh::lean_ctor_set(v___x_4134_, 3, v___x_4133_);
                crate::leanh::lean_ctor_set_uint8(
                    v___x_4134_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 4) as u32,
                    v___x_4131_,
                );
                return v___x_4134_;
            }
            3 => {
                v___x_4142_ = crate::leanh::lean_alloc_ctor(1, 4, (1) as u32);
                crate::leanh::lean_ctor_set(v___x_4142_, 0, v___y_4139_);
                crate::leanh::lean_ctor_set(v___x_4142_, 1, v_k_4113_);
                crate::leanh::lean_ctor_set(v___x_4142_, 2, v_v_4114_);
                crate::leanh::lean_ctor_set(v___x_4142_, 3, v_r_4115_);
                crate::leanh::lean_ctor_set_uint8(
                    v___x_4142_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 4) as u32,
                    v___y_4137_,
                );
                v___x_4143_ = crate::leanh::lean_alloc_ctor(1, 4, (1) as u32);
                crate::leanh::lean_ctor_set(v___x_4143_, 0, v___y_4141_);
                crate::leanh::lean_ctor_set(v___x_4143_, 1, v___y_4136_);
                crate::leanh::lean_ctor_set(v___x_4143_, 2, v___y_4138_);
                crate::leanh::lean_ctor_set(v___x_4143_, 3, v___x_4142_);
                crate::leanh::lean_ctor_set_uint8(
                    v___x_4143_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 4) as u32,
                    v___y_4140_,
                );
                return v___x_4143_;
            }
            4 => {
                v___x_4160_ = crate::leanh::lean_alloc_ctor(1, 4, (1) as u32);
                crate::leanh::lean_ctor_set(v___x_4160_, 0, v_a_4150_);
                crate::leanh::lean_ctor_set(v___x_4160_, 1, v_kx_4151_);
                crate::leanh::lean_ctor_set(v___x_4160_, 2, v_vx_4152_);
                crate::leanh::lean_ctor_set(v___x_4160_, 3, v_b_4153_);
                crate::leanh::lean_ctor_set_uint8(
                    v___x_4160_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 4) as u32,
                    v___y_4146_,
                );
                v___x_4161_ = crate::leanh::lean_alloc_ctor(1, 4, (1) as u32);
                crate::leanh::lean_ctor_set(v___x_4161_, 0, v_c_4156_);
                crate::leanh::lean_ctor_set(v___x_4161_, 1, v_kz_4157_);
                crate::leanh::lean_ctor_set(v___x_4161_, 2, v_vz_4158_);
                crate::leanh::lean_ctor_set(v___x_4161_, 3, v_d_4159_);
                crate::leanh::lean_ctor_set_uint8(
                    v___x_4161_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 4) as u32,
                    v___y_4146_,
                );
                v___x_4162_ = crate::leanh::lean_alloc_ctor(1, 4, (1) as u32);
                crate::leanh::lean_ctor_set(v___x_4162_, 0, v___x_4160_);
                crate::leanh::lean_ctor_set(v___x_4162_, 1, v_ky_4154_);
                crate::leanh::lean_ctor_set(v___x_4162_, 2, v_vy_4155_);
                crate::leanh::lean_ctor_set(v___x_4162_, 3, v___x_4161_);
                crate::leanh::lean_ctor_set_uint8(
                    v___x_4162_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 4) as u32,
                    v___y_4149_,
                );
                v___y_4136_ = v___y_4145_;
                v___y_4137_ = v___y_4146_;
                v___y_4138_ = v___y_4147_;
                v___y_4139_ = v___y_4148_;
                v___y_4140_ = v___y_4149_;
                v___y_4141_ = v___x_4162_;
                state = 3;
                continue;
            }
            5 => {
                v___x_4173_ = crate::leanh::lean_alloc_ctor(1, 4, (1) as u32);
                crate::leanh::lean_ctor_set(v___x_4173_, 0, v_a_4169_);
                crate::leanh::lean_ctor_set(v___x_4173_, 1, v_kx_4170_);
                crate::leanh::lean_ctor_set(v___x_4173_, 2, v_vx_4171_);
                crate::leanh::lean_ctor_set(v___x_4173_, 3, v_b_4172_);
                crate::leanh::lean_ctor_set_uint8(
                    v___x_4173_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 4) as u32,
                    v___y_4165_,
                );
                v___y_4136_ = v___y_4164_;
                v___y_4137_ = v___y_4165_;
                v___y_4138_ = v___y_4166_;
                v___y_4139_ = v___y_4167_;
                v___y_4140_ = v___y_4168_;
                v___y_4141_ = v___x_4173_;
                state = 3;
                continue;
            }
            6 => {
                if crate::leanh::lean_obj_tag(v_l_4112_) == 1 {
                    v_color_4175_ = crate::leanh::lean_ctor_get_uint8(
                        v_l_4112_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 4) as u32,
                    );
                    if v_color_4175_ == 0 {
                        v_rchild_4176_ = crate::leanh::lean_ctor_get(v_l_4112_, 3);
                        if crate::leanh::lean_obj_tag(v_rchild_4176_) == 1 {
                            v_color_4177_ = crate::leanh::lean_ctor_get_uint8(
                                v_rchild_4176_,
                                (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 4) as u32,
                            );
                            if v_color_4177_ == 1 {
                                crate::leanh::lean_inc_ref(v_rchild_4176_);
                                v_lchild_4178_ = crate::leanh::lean_ctor_get(v_l_4112_, 0);
                                crate::leanh::lean_inc(v_lchild_4178_);
                                v_key_4179_ = crate::leanh::lean_ctor_get(v_l_4112_, 1);
                                crate::leanh::lean_inc(v_key_4179_);
                                v_val_4180_ = crate::leanh::lean_ctor_get(v_l_4112_, 2);
                                crate::leanh::lean_inc(v_val_4180_);
                                crate::leanh::lean_dec_ref_known(v_l_4112_, 4);
                                v_lchild_4181_ = crate::leanh::lean_ctor_get(v_rchild_4176_, 0);
                                crate::leanh::lean_inc(v_lchild_4181_);
                                v_key_4182_ = crate::leanh::lean_ctor_get(v_rchild_4176_, 1);
                                crate::leanh::lean_inc(v_key_4182_);
                                v_val_4183_ = crate::leanh::lean_ctor_get(v_rchild_4176_, 2);
                                crate::leanh::lean_inc(v_val_4183_);
                                v_rchild_4184_ = crate::leanh::lean_ctor_get(v_rchild_4176_, 3);
                                crate::leanh::lean_inc(v_rchild_4184_);
                                crate::leanh::lean_dec_ref_known(v_rchild_4176_, 4);
                                v___x_4185_ = l_Lean_RBNode_setRed___redArg(v_lchild_4178_);
                                if crate::leanh::lean_obj_tag(v___x_4185_) == 1 {
                                    v_color_4186_ = crate::leanh::lean_ctor_get_uint8(
                                        v___x_4185_,
                                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 4)
                                            as u32,
                                    );
                                    if v_color_4186_ == 0 {
                                        v_lchild_4187_ =
                                            crate::leanh::lean_ctor_get(v___x_4185_, 0);
                                        crate::leanh::lean_inc(v_lchild_4187_);
                                        if crate::leanh::lean_obj_tag(v_lchild_4187_) == 1 {
                                            v_color_4188_ = crate::leanh::lean_ctor_get_uint8(
                                                v_lchild_4187_,
                                                (core::mem::size_of::<*mut crate::leanh::LeanObject>(
                                                ) * 4)
                                                    as u32,
                                            );
                                            if v_color_4188_ == 0 {
                                                v_key_4189_ =
                                                    crate::leanh::lean_ctor_get(v___x_4185_, 1);
                                                crate::leanh::lean_inc(v_key_4189_);
                                                v_val_4190_ =
                                                    crate::leanh::lean_ctor_get(v___x_4185_, 2);
                                                crate::leanh::lean_inc(v_val_4190_);
                                                v_rchild_4191_ =
                                                    crate::leanh::lean_ctor_get(v___x_4185_, 3);
                                                crate::leanh::lean_inc(v_rchild_4191_);
                                                crate::leanh::lean_dec_ref_known(v___x_4185_, 4);
                                                v_lchild_4192_ =
                                                    crate::leanh::lean_ctor_get(v_lchild_4187_, 0);
                                                crate::leanh::lean_inc(v_lchild_4192_);
                                                v_key_4193_ =
                                                    crate::leanh::lean_ctor_get(v_lchild_4187_, 1);
                                                crate::leanh::lean_inc(v_key_4193_);
                                                v_val_4194_ =
                                                    crate::leanh::lean_ctor_get(v_lchild_4187_, 2);
                                                crate::leanh::lean_inc(v_val_4194_);
                                                v_rchild_4195_ =
                                                    crate::leanh::lean_ctor_get(v_lchild_4187_, 3);
                                                crate::leanh::lean_inc(v_rchild_4195_);
                                                crate::leanh::lean_dec_ref_known(v_lchild_4187_, 4);
                                                v___y_4145_ = v_key_4182_;
                                                v___y_4146_ = v_color_4177_;
                                                v___y_4147_ = v_val_4183_;
                                                v___y_4148_ = v_rchild_4184_;
                                                v___y_4149_ = v_color_4175_;
                                                v_a_4150_ = v_lchild_4192_;
                                                v_kx_4151_ = v_key_4193_;
                                                v_vx_4152_ = v_val_4194_;
                                                v_b_4153_ = v_rchild_4195_;
                                                v_ky_4154_ = v_key_4189_;
                                                v_vy_4155_ = v_val_4190_;
                                                v_c_4156_ = v_rchild_4191_;
                                                v_kz_4157_ = v_key_4179_;
                                                v_vz_4158_ = v_val_4180_;
                                                v_d_4159_ = v_lchild_4181_;
                                                state = 4;
                                                continue;
                                            } else {
                                                v_rchild_4196_ =
                                                    crate::leanh::lean_ctor_get(v___x_4185_, 3);
                                                crate::leanh::lean_inc(v_rchild_4196_);
                                                if crate::leanh::lean_obj_tag(v_rchild_4196_) == 1 {
                                                    v_color_4197_ =
                                                        crate::leanh::lean_ctor_get_uint8(
                                                            v_rchild_4196_,
                                                            (core::mem::size_of::<
                                                                *mut crate::leanh::LeanObject,
                                                            >(
                                                            ) * 4)
                                                                as u32,
                                                        );
                                                    if v_color_4197_ == 0 {
                                                        v_key_4198_ = crate::leanh::lean_ctor_get(
                                                            v___x_4185_,
                                                            1,
                                                        );
                                                        crate::leanh::lean_inc(v_key_4198_);
                                                        v_val_4199_ = crate::leanh::lean_ctor_get(
                                                            v___x_4185_,
                                                            2,
                                                        );
                                                        crate::leanh::lean_inc(v_val_4199_);
                                                        crate::leanh::lean_dec_ref_known(
                                                            v___x_4185_,
                                                            4,
                                                        );
                                                        v_lchild_4200_ =
                                                            crate::leanh::lean_ctor_get(
                                                                v_rchild_4196_,
                                                                0,
                                                            );
                                                        crate::leanh::lean_inc(v_lchild_4200_);
                                                        v_key_4201_ = crate::leanh::lean_ctor_get(
                                                            v_rchild_4196_,
                                                            1,
                                                        );
                                                        crate::leanh::lean_inc(v_key_4201_);
                                                        v_val_4202_ = crate::leanh::lean_ctor_get(
                                                            v_rchild_4196_,
                                                            2,
                                                        );
                                                        crate::leanh::lean_inc(v_val_4202_);
                                                        v_rchild_4203_ =
                                                            crate::leanh::lean_ctor_get(
                                                                v_rchild_4196_,
                                                                3,
                                                            );
                                                        crate::leanh::lean_inc(v_rchild_4203_);
                                                        crate::leanh::lean_dec_ref_known(
                                                            v_rchild_4196_,
                                                            4,
                                                        );
                                                        v___y_4145_ = v_key_4182_;
                                                        v___y_4146_ = v_color_4177_;
                                                        v___y_4147_ = v_val_4183_;
                                                        v___y_4148_ = v_rchild_4184_;
                                                        v___y_4149_ = v_color_4175_;
                                                        v_a_4150_ = v_lchild_4187_;
                                                        v_kx_4151_ = v_key_4198_;
                                                        v_vx_4152_ = v_val_4199_;
                                                        v_b_4153_ = v_lchild_4200_;
                                                        v_ky_4154_ = v_key_4201_;
                                                        v_vy_4155_ = v_val_4202_;
                                                        v_c_4156_ = v_rchild_4203_;
                                                        v_kz_4157_ = v_key_4179_;
                                                        v_vz_4158_ = v_val_4180_;
                                                        v_d_4159_ = v_lchild_4181_;
                                                        state = 4;
                                                        continue;
                                                    } else {
                                                        crate::leanh::lean_dec_ref_known(
                                                            v_rchild_4196_,
                                                            4,
                                                        );
                                                        crate::leanh::lean_dec_ref_known(
                                                            v_lchild_4187_,
                                                            4,
                                                        );
                                                        v___y_4164_ = v_key_4182_;
                                                        v___y_4165_ = v_color_4177_;
                                                        v___y_4166_ = v_val_4183_;
                                                        v___y_4167_ = v_rchild_4184_;
                                                        v___y_4168_ = v_color_4175_;
                                                        v_a_4169_ = v___x_4185_;
                                                        v_kx_4170_ = v_key_4179_;
                                                        v_vx_4171_ = v_val_4180_;
                                                        v_b_4172_ = v_lchild_4181_;
                                                        state = 5;
                                                        continue;
                                                    }
                                                } else {
                                                    crate::leanh::lean_dec(v_rchild_4196_);
                                                    crate::leanh::lean_dec_ref_known(
                                                        v_lchild_4187_,
                                                        4,
                                                    );
                                                    v___y_4164_ = v_key_4182_;
                                                    v___y_4165_ = v_color_4177_;
                                                    v___y_4166_ = v_val_4183_;
                                                    v___y_4167_ = v_rchild_4184_;
                                                    v___y_4168_ = v_color_4175_;
                                                    v_a_4169_ = v___x_4185_;
                                                    v_kx_4170_ = v_key_4179_;
                                                    v_vx_4171_ = v_val_4180_;
                                                    v_b_4172_ = v_lchild_4181_;
                                                    state = 5;
                                                    continue;
                                                }
                                            }
                                        } else {
                                            v_rchild_4204_ =
                                                crate::leanh::lean_ctor_get(v___x_4185_, 3);
                                            crate::leanh::lean_inc(v_rchild_4204_);
                                            if crate::leanh::lean_obj_tag(v_rchild_4204_) == 1 {
                                                v_color_4205_ = crate::leanh::lean_ctor_get_uint8(
                                                    v_rchild_4204_,
                                                    (core::mem::size_of::<
                                                        *mut crate::leanh::LeanObject,
                                                    >(
                                                    ) * 4)
                                                        as u32,
                                                );
                                                if v_color_4205_ == 0 {
                                                    v_key_4206_ =
                                                        crate::leanh::lean_ctor_get(v___x_4185_, 1);
                                                    crate::leanh::lean_inc(v_key_4206_);
                                                    v_val_4207_ =
                                                        crate::leanh::lean_ctor_get(v___x_4185_, 2);
                                                    crate::leanh::lean_inc(v_val_4207_);
                                                    crate::leanh::lean_dec_ref_known(
                                                        v___x_4185_,
                                                        4,
                                                    );
                                                    v_lchild_4208_ = crate::leanh::lean_ctor_get(
                                                        v_rchild_4204_,
                                                        0,
                                                    );
                                                    crate::leanh::lean_inc(v_lchild_4208_);
                                                    v_key_4209_ = crate::leanh::lean_ctor_get(
                                                        v_rchild_4204_,
                                                        1,
                                                    );
                                                    crate::leanh::lean_inc(v_key_4209_);
                                                    v_val_4210_ = crate::leanh::lean_ctor_get(
                                                        v_rchild_4204_,
                                                        2,
                                                    );
                                                    crate::leanh::lean_inc(v_val_4210_);
                                                    v_rchild_4211_ = crate::leanh::lean_ctor_get(
                                                        v_rchild_4204_,
                                                        3,
                                                    );
                                                    crate::leanh::lean_inc(v_rchild_4211_);
                                                    crate::leanh::lean_dec_ref_known(
                                                        v_rchild_4204_,
                                                        4,
                                                    );
                                                    v___y_4145_ = v_key_4182_;
                                                    v___y_4146_ = v_color_4177_;
                                                    v___y_4147_ = v_val_4183_;
                                                    v___y_4148_ = v_rchild_4184_;
                                                    v___y_4149_ = v_color_4175_;
                                                    v_a_4150_ = v_lchild_4187_;
                                                    v_kx_4151_ = v_key_4206_;
                                                    v_vx_4152_ = v_val_4207_;
                                                    v_b_4153_ = v_lchild_4208_;
                                                    v_ky_4154_ = v_key_4209_;
                                                    v_vy_4155_ = v_val_4210_;
                                                    v_c_4156_ = v_rchild_4211_;
                                                    v_kz_4157_ = v_key_4179_;
                                                    v_vz_4158_ = v_val_4180_;
                                                    v_d_4159_ = v_lchild_4181_;
                                                    state = 4;
                                                    continue;
                                                } else {
                                                    crate::leanh::lean_dec_ref_known(
                                                        v_rchild_4204_,
                                                        4,
                                                    );
                                                    crate::leanh::lean_dec(v_lchild_4187_);
                                                    v___y_4164_ = v_key_4182_;
                                                    v___y_4165_ = v_color_4177_;
                                                    v___y_4166_ = v_val_4183_;
                                                    v___y_4167_ = v_rchild_4184_;
                                                    v___y_4168_ = v_color_4175_;
                                                    v_a_4169_ = v___x_4185_;
                                                    v_kx_4170_ = v_key_4179_;
                                                    v_vx_4171_ = v_val_4180_;
                                                    v_b_4172_ = v_lchild_4181_;
                                                    state = 5;
                                                    continue;
                                                }
                                            } else {
                                                crate::leanh::lean_dec(v_rchild_4204_);
                                                crate::leanh::lean_dec(v_lchild_4187_);
                                                v___y_4164_ = v_key_4182_;
                                                v___y_4165_ = v_color_4177_;
                                                v___y_4166_ = v_val_4183_;
                                                v___y_4167_ = v_rchild_4184_;
                                                v___y_4168_ = v_color_4175_;
                                                v_a_4169_ = v___x_4185_;
                                                v_kx_4170_ = v_key_4179_;
                                                v_vx_4171_ = v_val_4180_;
                                                v_b_4172_ = v_lchild_4181_;
                                                state = 5;
                                                continue;
                                            }
                                        }
                                    } else {
                                        v___y_4164_ = v_key_4182_;
                                        v___y_4165_ = v_color_4177_;
                                        v___y_4166_ = v_val_4183_;
                                        v___y_4167_ = v_rchild_4184_;
                                        v___y_4168_ = v_color_4175_;
                                        v_a_4169_ = v___x_4185_;
                                        v_kx_4170_ = v_key_4179_;
                                        v_vx_4171_ = v_val_4180_;
                                        v_b_4172_ = v_lchild_4181_;
                                        state = 5;
                                        continue;
                                    }
                                } else {
                                    v___y_4164_ = v_key_4182_;
                                    v___y_4165_ = v_color_4177_;
                                    v___y_4166_ = v_val_4183_;
                                    v___y_4167_ = v_rchild_4184_;
                                    v___y_4168_ = v_color_4175_;
                                    v_a_4169_ = v___x_4185_;
                                    v_kx_4170_ = v_key_4179_;
                                    v_vx_4171_ = v_val_4180_;
                                    v_b_4172_ = v_lchild_4181_;
                                    state = 5;
                                    continue;
                                }
                            } else {
                                state = 1;
                                continue;
                            }
                        } else {
                            state = 1;
                            continue;
                        }
                    } else {
                        v_lchild_4212_ = crate::leanh::lean_ctor_get(v_l_4112_, 0);
                        v_key_4213_ = crate::leanh::lean_ctor_get(v_l_4112_, 1);
                        v_val_4214_ = crate::leanh::lean_ctor_get(v_l_4112_, 2);
                        v_rchild_4215_ = crate::leanh::lean_ctor_get(v_l_4112_, 3);
                        v_isSharedCheck_4272_ = (!crate::leanh::lean_is_exclusive(v_l_4112_)) as u8;
                        if v_isSharedCheck_4272_ == 0 {
                            v___x_4217_ = v_l_4112_;
                            v_isShared_4218_ = v_isSharedCheck_4272_;
                            state = 7;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_rchild_4215_);
                            crate::leanh::lean_inc(v_val_4214_);
                            crate::leanh::lean_inc(v_key_4213_);
                            crate::leanh::lean_inc(v_lchild_4212_);
                            crate::leanh::lean_dec(v_l_4112_);
                            v___x_4217_ = crate::leanh::lean_box(0);
                            v_isShared_4218_ = v_isSharedCheck_4272_;
                            state = 7;
                            continue;
                        }
                    }
                } else {
                    state = 1;
                    continue;
                }
            }
            7 => {
                v___x_4219_ = 0;
                crate::leanh::lean_inc(v_rchild_4215_);
                crate::leanh::lean_inc(v_val_4214_);
                crate::leanh::lean_inc(v_key_4213_);
                crate::leanh::lean_inc(v_lchild_4212_);
                if v_isShared_4218_ == 0 {
                    v___x_4221_ = v___x_4217_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_4271_ = crate::leanh::lean_alloc_ctor(1, 4, (1) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4271_, 0, v_lchild_4212_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4271_, 1, v_key_4213_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4271_, 2, v_val_4214_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4271_, 3, v_rchild_4215_);
                    v___x_4221_ = v_reuseFailAlloc_4271_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                crate::leanh::lean_ctor_set_uint8(
                    v___x_4221_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 4) as u32,
                    v___x_4219_,
                );
                if crate::leanh::lean_obj_tag(v_lchild_4212_) == 1 {
                    v_color_4222_ = crate::leanh::lean_ctor_get_uint8(
                        v_lchild_4212_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 4) as u32,
                    );
                    if v_color_4222_ == 0 {
                        crate::leanh::lean_dec_ref(v___x_4221_);
                        v_lchild_4223_ = crate::leanh::lean_ctor_get(v_lchild_4212_, 0);
                        crate::leanh::lean_inc(v_lchild_4223_);
                        v_key_4224_ = crate::leanh::lean_ctor_get(v_lchild_4212_, 1);
                        crate::leanh::lean_inc(v_key_4224_);
                        v_val_4225_ = crate::leanh::lean_ctor_get(v_lchild_4212_, 2);
                        crate::leanh::lean_inc(v_val_4225_);
                        v_rchild_4226_ = crate::leanh::lean_ctor_get(v_lchild_4212_, 3);
                        crate::leanh::lean_inc(v_rchild_4226_);
                        crate::leanh::lean_dec_ref_known(v_lchild_4212_, 4);
                        v___y_4120_ = v_color_4175_;
                        v_a_4121_ = v_lchild_4223_;
                        v_kx_4122_ = v_key_4224_;
                        v_vx_4123_ = v_val_4225_;
                        v_b_4124_ = v_rchild_4226_;
                        v_ky_4125_ = v_key_4213_;
                        v_vy_4126_ = v_val_4214_;
                        v_c_4127_ = v_rchild_4215_;
                        v_kz_4128_ = v_k_4113_;
                        v_vz_4129_ = v_v_4114_;
                        v_d_4130_ = v_r_4115_;
                        state = 2;
                        continue;
                    } else {
                        if crate::leanh::lean_obj_tag(v_rchild_4215_) == 1 {
                            v_color_4227_ = crate::leanh::lean_ctor_get_uint8(
                                v_rchild_4215_,
                                (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 4) as u32,
                            );
                            if v_color_4227_ == 0 {
                                crate::leanh::lean_dec_ref(v___x_4221_);
                                v_lchild_4228_ = crate::leanh::lean_ctor_get(v_rchild_4215_, 0);
                                crate::leanh::lean_inc(v_lchild_4228_);
                                v_key_4229_ = crate::leanh::lean_ctor_get(v_rchild_4215_, 1);
                                crate::leanh::lean_inc(v_key_4229_);
                                v_val_4230_ = crate::leanh::lean_ctor_get(v_rchild_4215_, 2);
                                crate::leanh::lean_inc(v_val_4230_);
                                v_rchild_4231_ = crate::leanh::lean_ctor_get(v_rchild_4215_, 3);
                                crate::leanh::lean_inc(v_rchild_4231_);
                                crate::leanh::lean_dec_ref_known(v_rchild_4215_, 4);
                                v___y_4120_ = v_color_4175_;
                                v_a_4121_ = v_lchild_4212_;
                                v_kx_4122_ = v_key_4213_;
                                v_vx_4123_ = v_val_4214_;
                                v_b_4124_ = v_lchild_4228_;
                                v_ky_4125_ = v_key_4229_;
                                v_vy_4126_ = v_val_4230_;
                                v_c_4127_ = v_rchild_4231_;
                                v_kz_4128_ = v_k_4113_;
                                v_vz_4129_ = v_v_4114_;
                                v_d_4130_ = v_r_4115_;
                                state = 2;
                                continue;
                            } else {
                                crate::leanh::lean_dec_ref_known(v_lchild_4212_, 4);
                                crate::leanh::lean_dec(v_val_4214_);
                                crate::leanh::lean_dec(v_key_4213_);
                                v_isSharedCheck_4238_ =
                                    (!crate::leanh::lean_is_exclusive(v_rchild_4215_)) as u8;
                                if v_isSharedCheck_4238_ == 0 {
                                    v_unused_4239_ = crate::leanh::lean_ctor_get(v_rchild_4215_, 3);
                                    crate::leanh::lean_dec(v_unused_4239_);
                                    v_unused_4240_ = crate::leanh::lean_ctor_get(v_rchild_4215_, 2);
                                    crate::leanh::lean_dec(v_unused_4240_);
                                    v_unused_4241_ = crate::leanh::lean_ctor_get(v_rchild_4215_, 1);
                                    crate::leanh::lean_dec(v_unused_4241_);
                                    v_unused_4242_ = crate::leanh::lean_ctor_get(v_rchild_4215_, 0);
                                    crate::leanh::lean_dec(v_unused_4242_);
                                    v___x_4233_ = v_rchild_4215_;
                                    v_isShared_4234_ = v_isSharedCheck_4238_;
                                    state = 9;
                                    continue;
                                } else {
                                    crate::leanh::lean_dec(v_rchild_4215_);
                                    v___x_4233_ = crate::leanh::lean_box(0);
                                    v_isShared_4234_ = v_isSharedCheck_4238_;
                                    state = 9;
                                    continue;
                                }
                            }
                        } else {
                            crate::leanh::lean_dec(v_rchild_4215_);
                            crate::leanh::lean_dec(v_val_4214_);
                            crate::leanh::lean_dec(v_key_4213_);
                            v_isSharedCheck_4249_ =
                                (!crate::leanh::lean_is_exclusive(v_lchild_4212_)) as u8;
                            if v_isSharedCheck_4249_ == 0 {
                                v_unused_4250_ = crate::leanh::lean_ctor_get(v_lchild_4212_, 3);
                                crate::leanh::lean_dec(v_unused_4250_);
                                v_unused_4251_ = crate::leanh::lean_ctor_get(v_lchild_4212_, 2);
                                crate::leanh::lean_dec(v_unused_4251_);
                                v_unused_4252_ = crate::leanh::lean_ctor_get(v_lchild_4212_, 1);
                                crate::leanh::lean_dec(v_unused_4252_);
                                v_unused_4253_ = crate::leanh::lean_ctor_get(v_lchild_4212_, 0);
                                crate::leanh::lean_dec(v_unused_4253_);
                                v___x_4244_ = v_lchild_4212_;
                                v_isShared_4245_ = v_isSharedCheck_4249_;
                                state = 11;
                                continue;
                            } else {
                                crate::leanh::lean_dec(v_lchild_4212_);
                                v___x_4244_ = crate::leanh::lean_box(0);
                                v_isShared_4245_ = v_isSharedCheck_4249_;
                                state = 11;
                                continue;
                            }
                        }
                    }
                } else {
                    if crate::leanh::lean_obj_tag(v_rchild_4215_) == 1 {
                        v_color_4254_ = crate::leanh::lean_ctor_get_uint8(
                            v_rchild_4215_,
                            (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 4) as u32,
                        );
                        if v_color_4254_ == 0 {
                            crate::leanh::lean_dec_ref(v___x_4221_);
                            v_lchild_4255_ = crate::leanh::lean_ctor_get(v_rchild_4215_, 0);
                            crate::leanh::lean_inc(v_lchild_4255_);
                            v_key_4256_ = crate::leanh::lean_ctor_get(v_rchild_4215_, 1);
                            crate::leanh::lean_inc(v_key_4256_);
                            v_val_4257_ = crate::leanh::lean_ctor_get(v_rchild_4215_, 2);
                            crate::leanh::lean_inc(v_val_4257_);
                            v_rchild_4258_ = crate::leanh::lean_ctor_get(v_rchild_4215_, 3);
                            crate::leanh::lean_inc(v_rchild_4258_);
                            crate::leanh::lean_dec_ref_known(v_rchild_4215_, 4);
                            v___y_4120_ = v_color_4175_;
                            v_a_4121_ = v_lchild_4212_;
                            v_kx_4122_ = v_key_4213_;
                            v_vx_4123_ = v_val_4214_;
                            v_b_4124_ = v_lchild_4255_;
                            v_ky_4125_ = v_key_4256_;
                            v_vy_4126_ = v_val_4257_;
                            v_c_4127_ = v_rchild_4258_;
                            v_kz_4128_ = v_k_4113_;
                            v_vz_4129_ = v_v_4114_;
                            v_d_4130_ = v_r_4115_;
                            state = 2;
                            continue;
                        } else {
                            crate::leanh::lean_dec(v_val_4214_);
                            crate::leanh::lean_dec(v_key_4213_);
                            crate::leanh::lean_dec(v_lchild_4212_);
                            v_isSharedCheck_4265_ =
                                (!crate::leanh::lean_is_exclusive(v_rchild_4215_)) as u8;
                            if v_isSharedCheck_4265_ == 0 {
                                v_unused_4266_ = crate::leanh::lean_ctor_get(v_rchild_4215_, 3);
                                crate::leanh::lean_dec(v_unused_4266_);
                                v_unused_4267_ = crate::leanh::lean_ctor_get(v_rchild_4215_, 2);
                                crate::leanh::lean_dec(v_unused_4267_);
                                v_unused_4268_ = crate::leanh::lean_ctor_get(v_rchild_4215_, 1);
                                crate::leanh::lean_dec(v_unused_4268_);
                                v_unused_4269_ = crate::leanh::lean_ctor_get(v_rchild_4215_, 0);
                                crate::leanh::lean_dec(v_unused_4269_);
                                v___x_4260_ = v_rchild_4215_;
                                v_isShared_4261_ = v_isSharedCheck_4265_;
                                state = 13;
                                continue;
                            } else {
                                crate::leanh::lean_dec(v_rchild_4215_);
                                v___x_4260_ = crate::leanh::lean_box(0);
                                v_isShared_4261_ = v_isSharedCheck_4265_;
                                state = 13;
                                continue;
                            }
                        }
                    } else {
                        crate::leanh::lean_dec(v_rchild_4215_);
                        crate::leanh::lean_dec(v_val_4214_);
                        crate::leanh::lean_dec(v_key_4213_);
                        crate::leanh::lean_dec(v_lchild_4212_);
                        v___x_4270_ = crate::leanh::lean_alloc_ctor(1, 4, (1) as u32);
                        crate::leanh::lean_ctor_set(v___x_4270_, 0, v___x_4221_);
                        crate::leanh::lean_ctor_set(v___x_4270_, 1, v_k_4113_);
                        crate::leanh::lean_ctor_set(v___x_4270_, 2, v_v_4114_);
                        crate::leanh::lean_ctor_set(v___x_4270_, 3, v_r_4115_);
                        crate::leanh::lean_ctor_set_uint8(
                            v___x_4270_,
                            (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 4) as u32,
                            v_color_4175_,
                        );
                        return v___x_4270_;
                    }
                }
            }
            9 => {
                if v_isShared_4234_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4233_, 3, v_r_4115_);
                    crate::leanh::lean_ctor_set(v___x_4233_, 2, v_v_4114_);
                    crate::leanh::lean_ctor_set(v___x_4233_, 1, v_k_4113_);
                    crate::leanh::lean_ctor_set(v___x_4233_, 0, v___x_4221_);
                    v___x_4236_ = v___x_4233_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_4237_ = crate::leanh::lean_alloc_ctor(1, 4, (1) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4237_, 0, v___x_4221_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4237_, 1, v_k_4113_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4237_, 2, v_v_4114_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4237_, 3, v_r_4115_);
                    v___x_4236_ = v_reuseFailAlloc_4237_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                crate::leanh::lean_ctor_set_uint8(
                    v___x_4236_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 4) as u32,
                    v_color_4175_,
                );
                return v___x_4236_;
            }
            11 => {
                if v_isShared_4245_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4244_, 3, v_r_4115_);
                    crate::leanh::lean_ctor_set(v___x_4244_, 2, v_v_4114_);
                    crate::leanh::lean_ctor_set(v___x_4244_, 1, v_k_4113_);
                    crate::leanh::lean_ctor_set(v___x_4244_, 0, v___x_4221_);
                    v___x_4247_ = v___x_4244_;
                    state = 12;
                    continue;
                } else {
                    v_reuseFailAlloc_4248_ = crate::leanh::lean_alloc_ctor(1, 4, (1) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4248_, 0, v___x_4221_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4248_, 1, v_k_4113_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4248_, 2, v_v_4114_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4248_, 3, v_r_4115_);
                    v___x_4247_ = v_reuseFailAlloc_4248_;
                    state = 12;
                    continue;
                }
            }
            12 => {
                crate::leanh::lean_ctor_set_uint8(
                    v___x_4247_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 4) as u32,
                    v_color_4175_,
                );
                return v___x_4247_;
            }
            13 => {
                if v_isShared_4261_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4260_, 3, v_r_4115_);
                    crate::leanh::lean_ctor_set(v___x_4260_, 2, v_v_4114_);
                    crate::leanh::lean_ctor_set(v___x_4260_, 1, v_k_4113_);
                    crate::leanh::lean_ctor_set(v___x_4260_, 0, v___x_4221_);
                    v___x_4263_ = v___x_4260_;
                    state = 14;
                    continue;
                } else {
                    v_reuseFailAlloc_4264_ = crate::leanh::lean_alloc_ctor(1, 4, (1) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4264_, 0, v___x_4221_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4264_, 1, v_k_4113_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4264_, 2, v_v_4114_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4264_, 3, v_r_4115_);
                    v___x_4263_ = v_reuseFailAlloc_4264_;
                    state = 14;
                    continue;
                }
            }
            14 => {
                crate::leanh::lean_ctor_set_uint8(
                    v___x_4263_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 4) as u32,
                    v_color_4175_,
                );
                return v___x_4263_;
            }
            15 => {
                v___x_4281_ = 1;
                if v_isShared_4280_ == 0 {
                    v___x_4283_ = v___x_4279_;
                    state = 16;
                    continue;
                } else {
                    v_reuseFailAlloc_4285_ = crate::leanh::lean_alloc_ctor(1, 4, (1) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4285_, 0, v_lchild_4274_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4285_, 1, v_key_4275_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4285_, 2, v_val_4276_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4285_, 3, v_rchild_4277_);
                    v___x_4283_ = v_reuseFailAlloc_4285_;
                    state = 16;
                    continue;
                }
            }
            16 => {
                crate::leanh::lean_ctor_set_uint8(
                    v___x_4283_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 4) as u32,
                    v___x_4281_,
                );
                v___x_4284_ = crate::leanh::lean_alloc_ctor(1, 4, (1) as u32);
                crate::leanh::lean_ctor_set(v___x_4284_, 0, v_l_4112_);
                crate::leanh::lean_ctor_set(v___x_4284_, 1, v_k_4113_);
                crate::leanh::lean_ctor_set(v___x_4284_, 2, v_v_4114_);
                crate::leanh::lean_ctor_set(v___x_4284_, 3, v___x_4283_);
                crate::leanh::lean_ctor_set_uint8(
                    v___x_4284_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 4) as u32,
                    v_color_4273_,
                );
                return v___x_4284_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_RBNode_balRight(
    mut v_00_u03b1_4287_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_4288_: *mut crate::leanh::LeanObject,
    mut v_l_4289_: *mut crate::leanh::LeanObject,
    mut v_k_4290_: *mut crate::leanh::LeanObject,
    mut v_v_4291_: *mut crate::leanh::LeanObject,
    mut v_r_4292_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4293_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4293_ = l_Lean_RBNode_balRight___redArg(v_l_4289_, v_k_4290_, v_v_4291_, v_r_4292_);
    return v___x_4293_;
}
pub unsafe fn l_Lean_RBNode_size___redArg(
    mut v_x_4294_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_4294_) == 0 {
        let mut v___x_4295_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_4295_ = crate::leanh::lean_unsigned_to_nat(0);
        return v___x_4295_;
    } else {
        let mut v_lchild_4296_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_rchild_4297_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4298_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4299_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4300_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4301_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4302_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_lchild_4296_ = crate::leanh::lean_ctor_get(v_x_4294_, 0);
        v_rchild_4297_ = crate::leanh::lean_ctor_get(v_x_4294_, 3);
        v___x_4298_ = l_Lean_RBNode_size___redArg(v_lchild_4296_);
        v___x_4299_ = l_Lean_RBNode_size___redArg(v_rchild_4297_);
        v___x_4300_ = lean_nat_add(v___x_4298_, v___x_4299_);
        crate::leanh::lean_dec(v___x_4299_);
        crate::leanh::lean_dec(v___x_4298_);
        v___x_4301_ = crate::leanh::lean_unsigned_to_nat(1);
        v___x_4302_ = lean_nat_add(v___x_4300_, v___x_4301_);
        crate::leanh::lean_dec(v___x_4300_);
        return v___x_4302_;
    }
}
pub unsafe fn l_Lean_RBNode_size___redArg___boxed(
    mut v_x_4303_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4304_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4304_ = l_Lean_RBNode_size___redArg(v_x_4303_);
    crate::leanh::lean_dec(v_x_4303_);
    return v_res_4304_;
}
pub unsafe fn l_Lean_RBNode_size(
    mut v_00_u03b1_4305_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_4306_: *mut crate::leanh::LeanObject,
    mut v_x_4307_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4308_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4308_ = l_Lean_RBNode_size___redArg(v_x_4307_);
    return v___x_4308_;
}
pub unsafe fn l_Lean_RBNode_size___boxed(
    mut v_00_u03b1_4309_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_4310_: *mut crate::leanh::LeanObject,
    mut v_x_4311_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4312_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4312_ = l_Lean_RBNode_size(v_00_u03b1_4309_, v_00_u03b2_4310_, v_x_4311_);
    crate::leanh::lean_dec(v_x_4311_);
    return v_res_4312_;
}
pub unsafe fn l___private_Lean_Data_RBMap_0__Lean_RBNode_depth_match__1_splitter___redArg(
    mut v_x_4313_: *mut crate::leanh::LeanObject,
    mut v_h__1_4314_: *mut crate::leanh::LeanObject,
    mut v_h__2_4315_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_4313_) == 0 {
        let mut v___x_4316_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4317_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__2_4315_);
        v___x_4316_ = crate::leanh::lean_box(0);
        v___x_4317_ = crate::leanh::lean_apply_1(v_h__1_4314_, v___x_4316_);
        return v___x_4317_;
    } else {
        let mut v_color_4318_: u8 = 0;
        let mut v_lchild_4319_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_key_4320_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_val_4321_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_rchild_4322_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4323_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4324_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_4314_);
        v_color_4318_ = crate::leanh::lean_ctor_get_uint8(
            v_x_4313_,
            (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 4) as u32,
        );
        v_lchild_4319_ = crate::leanh::lean_ctor_get(v_x_4313_, 0);
        crate::leanh::lean_inc(v_lchild_4319_);
        v_key_4320_ = crate::leanh::lean_ctor_get(v_x_4313_, 1);
        crate::leanh::lean_inc(v_key_4320_);
        v_val_4321_ = crate::leanh::lean_ctor_get(v_x_4313_, 2);
        crate::leanh::lean_inc(v_val_4321_);
        v_rchild_4322_ = crate::leanh::lean_ctor_get(v_x_4313_, 3);
        crate::leanh::lean_inc(v_rchild_4322_);
        crate::leanh::lean_dec_ref_known(v_x_4313_, 4);
        v___x_4323_ = crate::leanh::lean_box((v_color_4318_) as usize);
        v___x_4324_ = crate::leanh::lean_apply_5(
            v_h__2_4315_,
            v___x_4323_,
            v_lchild_4319_,
            v_key_4320_,
            v_val_4321_,
            v_rchild_4322_,
        );
        return v___x_4324_;
    }
}
pub unsafe fn l___private_Lean_Data_RBMap_0__Lean_RBNode_depth_match__1_splitter(
    mut v_00_u03b1_4325_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_4326_: *mut crate::leanh::LeanObject,
    mut v_motive_4327_: *mut crate::leanh::LeanObject,
    mut v_x_4328_: *mut crate::leanh::LeanObject,
    mut v_h__1_4329_: *mut crate::leanh::LeanObject,
    mut v_h__2_4330_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_4328_) == 0 {
        let mut v___x_4331_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4332_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__2_4330_);
        v___x_4331_ = crate::leanh::lean_box(0);
        v___x_4332_ = crate::leanh::lean_apply_1(v_h__1_4329_, v___x_4331_);
        return v___x_4332_;
    } else {
        let mut v_color_4333_: u8 = 0;
        let mut v_lchild_4334_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_key_4335_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_val_4336_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_rchild_4337_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4338_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4339_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_4329_);
        v_color_4333_ = crate::leanh::lean_ctor_get_uint8(
            v_x_4328_,
            (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 4) as u32,
        );
        v_lchild_4334_ = crate::leanh::lean_ctor_get(v_x_4328_, 0);
        crate::leanh::lean_inc(v_lchild_4334_);
        v_key_4335_ = crate::leanh::lean_ctor_get(v_x_4328_, 1);
        crate::leanh::lean_inc(v_key_4335_);
        v_val_4336_ = crate::leanh::lean_ctor_get(v_x_4328_, 2);
        crate::leanh::lean_inc(v_val_4336_);
        v_rchild_4337_ = crate::leanh::lean_ctor_get(v_x_4328_, 3);
        crate::leanh::lean_inc(v_rchild_4337_);
        crate::leanh::lean_dec_ref_known(v_x_4328_, 4);
        v___x_4338_ = crate::leanh::lean_box((v_color_4333_) as usize);
        v___x_4339_ = crate::leanh::lean_apply_5(
            v_h__2_4330_,
            v___x_4338_,
            v_lchild_4334_,
            v_key_4335_,
            v_val_4336_,
            v_rchild_4337_,
        );
        return v___x_4339_;
    }
}
pub unsafe fn l_Lean_RBNode_appendTrees___redArg(
    mut v_x_4340_: *mut crate::leanh::LeanObject,
    mut v_x_4341_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_color_4342_: u8 = 0;
    let mut v_lchild_4343_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_key_4344_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_4345_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_rchild_4346_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_color_4347_: u8 = 0;
    let mut v_lchild_4348_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_key_4349_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_4350_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_rchild_4351_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_bc_4353_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4354_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4355_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_bc_4357_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4358_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4359_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4361_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4362_: u8 = 0;
    let mut v___x_4364_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4365_: u8 = 0;
    let mut v___x_4366_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_color_4367_: u8 = 0;
    let mut v_lchild_4368_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_key_4369_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_4370_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_rchild_4371_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4373_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4374_: u8 = 0;
    let mut v___x_4376_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4378_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4380_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4381_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4382_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4383_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4384_: u8 = 0;
    let mut v_isSharedCheck_4385_: u8 = 0;
    let mut v_unused_4386_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_4387_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_4388_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_4389_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4390_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4392_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4393_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4394_: u8 = 0;
    let mut v_unused_4395_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_4396_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_4397_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_4398_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4400_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4401_: u8 = 0;
    let mut v___x_4402_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4404_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4405_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4407_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4408_: u8 = 0;
    let mut v___x_4409_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_color_4410_: u8 = 0;
    let mut v_lchild_4411_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_key_4412_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_4413_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_rchild_4414_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4416_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4417_: u8 = 0;
    let mut v___x_4419_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4421_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4423_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4424_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4425_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4426_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4427_: u8 = 0;
    let mut v_isSharedCheck_4428_: u8 = 0;
    let mut v_unused_4429_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_4430_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_4431_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_4432_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4433_: u8 = 0;
    let mut v_unused_4434_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_4435_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_4436_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_4437_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_4340_) == 0 {
                    return v_x_4341_;
                } else {
                    if crate::leanh::lean_obj_tag(v_x_4341_) == 0 {
                        return v_x_4340_;
                    } else {
                        v_color_4342_ = crate::leanh::lean_ctor_get_uint8(
                            v_x_4340_,
                            (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 4) as u32,
                        );
                        v_lchild_4343_ = crate::leanh::lean_ctor_get(v_x_4340_, 0);
                        v_key_4344_ = crate::leanh::lean_ctor_get(v_x_4340_, 1);
                        v_val_4345_ = crate::leanh::lean_ctor_get(v_x_4340_, 2);
                        v_rchild_4346_ = crate::leanh::lean_ctor_get(v_x_4340_, 3);
                        v_color_4347_ = crate::leanh::lean_ctor_get_uint8(
                            v_x_4341_,
                            (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 4) as u32,
                        );
                        v_lchild_4348_ = crate::leanh::lean_ctor_get(v_x_4341_, 0);
                        v_key_4349_ = crate::leanh::lean_ctor_get(v_x_4341_, 1);
                        v_val_4350_ = crate::leanh::lean_ctor_get(v_x_4341_, 2);
                        v_rchild_4351_ = crate::leanh::lean_ctor_get(v_x_4341_, 3);
                        if v_color_4347_ == 0 {
                            crate::leanh::lean_inc(v_rchild_4351_);
                            crate::leanh::lean_inc(v_val_4350_);
                            crate::leanh::lean_inc(v_key_4349_);
                            crate::leanh::lean_inc(v_lchild_4348_);
                            v_isSharedCheck_4394_ =
                                (!crate::leanh::lean_is_exclusive(v_x_4341_)) as u8;
                            if v_isSharedCheck_4394_ == 0 {
                                v_unused_4395_ = crate::leanh::lean_ctor_get(v_x_4341_, 3);
                                crate::leanh::lean_dec(v_unused_4395_);
                                v_unused_4396_ = crate::leanh::lean_ctor_get(v_x_4341_, 2);
                                crate::leanh::lean_dec(v_unused_4396_);
                                v_unused_4397_ = crate::leanh::lean_ctor_get(v_x_4341_, 1);
                                crate::leanh::lean_dec(v_unused_4397_);
                                v_unused_4398_ = crate::leanh::lean_ctor_get(v_x_4341_, 0);
                                crate::leanh::lean_dec(v_unused_4398_);
                                v___x_4361_ = v_x_4341_;
                                v_isShared_4362_ = v_isSharedCheck_4394_;
                                state = 3;
                                continue;
                            } else {
                                crate::leanh::lean_dec(v_x_4341_);
                                v___x_4361_ = crate::leanh::lean_box(0);
                                v_isShared_4362_ = v_isSharedCheck_4394_;
                                state = 3;
                                continue;
                            }
                        } else {
                            crate::leanh::lean_inc(v_rchild_4346_);
                            crate::leanh::lean_inc(v_val_4345_);
                            crate::leanh::lean_inc(v_key_4344_);
                            crate::leanh::lean_inc(v_lchild_4343_);
                            v_isSharedCheck_4433_ =
                                (!crate::leanh::lean_is_exclusive(v_x_4340_)) as u8;
                            if v_isSharedCheck_4433_ == 0 {
                                v_unused_4434_ = crate::leanh::lean_ctor_get(v_x_4340_, 3);
                                crate::leanh::lean_dec(v_unused_4434_);
                                v_unused_4435_ = crate::leanh::lean_ctor_get(v_x_4340_, 2);
                                crate::leanh::lean_dec(v_unused_4435_);
                                v_unused_4436_ = crate::leanh::lean_ctor_get(v_x_4340_, 1);
                                crate::leanh::lean_dec(v_unused_4436_);
                                v_unused_4437_ = crate::leanh::lean_ctor_get(v_x_4340_, 0);
                                crate::leanh::lean_dec(v_unused_4437_);
                                v___x_4400_ = v_x_4340_;
                                v_isShared_4401_ = v_isSharedCheck_4433_;
                                state = 10;
                                continue;
                            } else {
                                crate::leanh::lean_dec(v_x_4340_);
                                v___x_4400_ = crate::leanh::lean_box(0);
                                v_isShared_4401_ = v_isSharedCheck_4433_;
                                state = 10;
                                continue;
                            }
                        }
                    }
                }
            }
            1 => {
                v___x_4354_ = crate::leanh::lean_alloc_ctor(1, 4, (1) as u32);
                crate::leanh::lean_ctor_set(v___x_4354_, 0, v_bc_4353_);
                crate::leanh::lean_ctor_set(v___x_4354_, 1, v_key_4349_);
                crate::leanh::lean_ctor_set(v___x_4354_, 2, v_val_4350_);
                crate::leanh::lean_ctor_set(v___x_4354_, 3, v_rchild_4351_);
                crate::leanh::lean_ctor_set_uint8(
                    v___x_4354_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 4) as u32,
                    v_color_4342_,
                );
                v___x_4355_ = l_Lean_RBNode_balLeft___redArg(
                    v_lchild_4343_,
                    v_key_4344_,
                    v_val_4345_,
                    v___x_4354_,
                );
                return v___x_4355_;
            }
            2 => {
                v___x_4358_ = crate::leanh::lean_alloc_ctor(1, 4, (1) as u32);
                crate::leanh::lean_ctor_set(v___x_4358_, 0, v_bc_4357_);
                crate::leanh::lean_ctor_set(v___x_4358_, 1, v_key_4349_);
                crate::leanh::lean_ctor_set(v___x_4358_, 2, v_val_4350_);
                crate::leanh::lean_ctor_set(v___x_4358_, 3, v_rchild_4351_);
                crate::leanh::lean_ctor_set_uint8(
                    v___x_4358_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 4) as u32,
                    v_color_4342_,
                );
                v___x_4359_ = crate::leanh::lean_alloc_ctor(1, 4, (1) as u32);
                crate::leanh::lean_ctor_set(v___x_4359_, 0, v_lchild_4343_);
                crate::leanh::lean_ctor_set(v___x_4359_, 1, v_key_4344_);
                crate::leanh::lean_ctor_set(v___x_4359_, 2, v_val_4345_);
                crate::leanh::lean_ctor_set(v___x_4359_, 3, v___x_4358_);
                crate::leanh::lean_ctor_set_uint8(
                    v___x_4359_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 4) as u32,
                    v_color_4342_,
                );
                return v___x_4359_;
            }
            3 => {
                if v_color_4342_ == 0 {
                    crate::leanh::lean_inc(v_rchild_4346_);
                    crate::leanh::lean_inc(v_val_4345_);
                    crate::leanh::lean_inc(v_key_4344_);
                    crate::leanh::lean_inc(v_lchild_4343_);
                    v_isSharedCheck_4385_ = (!crate::leanh::lean_is_exclusive(v_x_4340_)) as u8;
                    if v_isSharedCheck_4385_ == 0 {
                        v_unused_4386_ = crate::leanh::lean_ctor_get(v_x_4340_, 3);
                        crate::leanh::lean_dec(v_unused_4386_);
                        v_unused_4387_ = crate::leanh::lean_ctor_get(v_x_4340_, 2);
                        crate::leanh::lean_dec(v_unused_4387_);
                        v_unused_4388_ = crate::leanh::lean_ctor_get(v_x_4340_, 1);
                        crate::leanh::lean_dec(v_unused_4388_);
                        v_unused_4389_ = crate::leanh::lean_ctor_get(v_x_4340_, 0);
                        crate::leanh::lean_dec(v_unused_4389_);
                        v___x_4364_ = v_x_4340_;
                        v_isShared_4365_ = v_isSharedCheck_4385_;
                        state = 4;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v_x_4340_);
                        v___x_4364_ = crate::leanh::lean_box(0);
                        v_isShared_4365_ = v_isSharedCheck_4385_;
                        state = 4;
                        continue;
                    }
                } else {
                    v___x_4390_ = l_Lean_RBNode_appendTrees___redArg(v_x_4340_, v_lchild_4348_);
                    if v_isShared_4362_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_4361_, 0, v___x_4390_);
                        v___x_4392_ = v___x_4361_;
                        state = 9;
                        continue;
                    } else {
                        v_reuseFailAlloc_4393_ = crate::leanh::lean_alloc_ctor(1, 4, (1) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_4393_, 0, v___x_4390_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_4393_, 1, v_key_4349_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_4393_, 2, v_val_4350_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_4393_, 3, v_rchild_4351_);
                        crate::leanh::lean_ctor_set_uint8(
                            v_reuseFailAlloc_4393_,
                            (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 4) as u32,
                            v_color_4347_,
                        );
                        v___x_4392_ = v_reuseFailAlloc_4393_;
                        state = 9;
                        continue;
                    }
                }
            }
            4 => {
                v___x_4366_ = l_Lean_RBNode_appendTrees___redArg(v_rchild_4346_, v_lchild_4348_);
                if crate::leanh::lean_obj_tag(v___x_4366_) == 1 {
                    v_color_4367_ = crate::leanh::lean_ctor_get_uint8(
                        v___x_4366_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 4) as u32,
                    );
                    if v_color_4367_ == 0 {
                        v_lchild_4368_ = crate::leanh::lean_ctor_get(v___x_4366_, 0);
                        v_key_4369_ = crate::leanh::lean_ctor_get(v___x_4366_, 1);
                        v_val_4370_ = crate::leanh::lean_ctor_get(v___x_4366_, 2);
                        v_rchild_4371_ = crate::leanh::lean_ctor_get(v___x_4366_, 3);
                        v_isSharedCheck_4384_ =
                            (!crate::leanh::lean_is_exclusive(v___x_4366_)) as u8;
                        if v_isSharedCheck_4384_ == 0 {
                            v___x_4373_ = v___x_4366_;
                            v_isShared_4374_ = v_isSharedCheck_4384_;
                            state = 5;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_rchild_4371_);
                            crate::leanh::lean_inc(v_val_4370_);
                            crate::leanh::lean_inc(v_key_4369_);
                            crate::leanh::lean_inc(v_lchild_4368_);
                            crate::leanh::lean_dec(v___x_4366_);
                            v___x_4373_ = crate::leanh::lean_box(0);
                            v_isShared_4374_ = v_isSharedCheck_4384_;
                            state = 5;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_del_object(v___x_4364_);
                        crate::leanh::lean_del_object(v___x_4361_);
                        v_bc_4357_ = v___x_4366_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_4364_);
                    crate::leanh::lean_del_object(v___x_4361_);
                    v_bc_4357_ = v___x_4366_;
                    state = 2;
                    continue;
                }
            }
            5 => {
                if v_isShared_4374_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4373_, 3, v_lchild_4368_);
                    crate::leanh::lean_ctor_set(v___x_4373_, 2, v_val_4345_);
                    crate::leanh::lean_ctor_set(v___x_4373_, 1, v_key_4344_);
                    crate::leanh::lean_ctor_set(v___x_4373_, 0, v_lchild_4343_);
                    v___x_4376_ = v___x_4373_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_4383_ = crate::leanh::lean_alloc_ctor(1, 4, (1) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4383_, 0, v_lchild_4343_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4383_, 1, v_key_4344_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4383_, 2, v_val_4345_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4383_, 3, v_lchild_4368_);
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_4383_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 4) as u32,
                        v_color_4367_,
                    );
                    v___x_4376_ = v_reuseFailAlloc_4383_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                if v_isShared_4362_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4361_, 0, v_rchild_4371_);
                    v___x_4378_ = v___x_4361_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_4382_ = crate::leanh::lean_alloc_ctor(1, 4, (1) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4382_, 0, v_rchild_4371_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4382_, 1, v_key_4349_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4382_, 2, v_val_4350_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4382_, 3, v_rchild_4351_);
                    v___x_4378_ = v_reuseFailAlloc_4382_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                crate::leanh::lean_ctor_set_uint8(
                    v___x_4378_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 4) as u32,
                    v_color_4367_,
                );
                if v_isShared_4365_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4364_, 3, v___x_4378_);
                    crate::leanh::lean_ctor_set(v___x_4364_, 2, v_val_4370_);
                    crate::leanh::lean_ctor_set(v___x_4364_, 1, v_key_4369_);
                    crate::leanh::lean_ctor_set(v___x_4364_, 0, v___x_4376_);
                    v___x_4380_ = v___x_4364_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_4381_ = crate::leanh::lean_alloc_ctor(1, 4, (1) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4381_, 0, v___x_4376_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4381_, 1, v_key_4369_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4381_, 2, v_val_4370_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4381_, 3, v___x_4378_);
                    v___x_4380_ = v_reuseFailAlloc_4381_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                crate::leanh::lean_ctor_set_uint8(
                    v___x_4380_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 4) as u32,
                    v_color_4367_,
                );
                return v___x_4380_;
            }
            9 => {
                return v___x_4392_;
            }
            10 => {
                if v_color_4342_ == 0 {
                    v___x_4402_ = l_Lean_RBNode_appendTrees___redArg(v_rchild_4346_, v_x_4341_);
                    if v_isShared_4401_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_4400_, 3, v___x_4402_);
                        v___x_4404_ = v___x_4400_;
                        state = 11;
                        continue;
                    } else {
                        v_reuseFailAlloc_4405_ = crate::leanh::lean_alloc_ctor(1, 4, (1) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_4405_, 0, v_lchild_4343_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_4405_, 1, v_key_4344_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_4405_, 2, v_val_4345_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_4405_, 3, v___x_4402_);
                        crate::leanh::lean_ctor_set_uint8(
                            v_reuseFailAlloc_4405_,
                            (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 4) as u32,
                            v_color_4342_,
                        );
                        v___x_4404_ = v_reuseFailAlloc_4405_;
                        state = 11;
                        continue;
                    }
                } else {
                    crate::leanh::lean_inc(v_rchild_4351_);
                    crate::leanh::lean_inc(v_val_4350_);
                    crate::leanh::lean_inc(v_key_4349_);
                    crate::leanh::lean_inc(v_lchild_4348_);
                    v_isSharedCheck_4428_ = (!crate::leanh::lean_is_exclusive(v_x_4341_)) as u8;
                    if v_isSharedCheck_4428_ == 0 {
                        v_unused_4429_ = crate::leanh::lean_ctor_get(v_x_4341_, 3);
                        crate::leanh::lean_dec(v_unused_4429_);
                        v_unused_4430_ = crate::leanh::lean_ctor_get(v_x_4341_, 2);
                        crate::leanh::lean_dec(v_unused_4430_);
                        v_unused_4431_ = crate::leanh::lean_ctor_get(v_x_4341_, 1);
                        crate::leanh::lean_dec(v_unused_4431_);
                        v_unused_4432_ = crate::leanh::lean_ctor_get(v_x_4341_, 0);
                        crate::leanh::lean_dec(v_unused_4432_);
                        v___x_4407_ = v_x_4341_;
                        v_isShared_4408_ = v_isSharedCheck_4428_;
                        state = 12;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v_x_4341_);
                        v___x_4407_ = crate::leanh::lean_box(0);
                        v_isShared_4408_ = v_isSharedCheck_4428_;
                        state = 12;
                        continue;
                    }
                }
            }
            11 => {
                return v___x_4404_;
            }
            12 => {
                v___x_4409_ = l_Lean_RBNode_appendTrees___redArg(v_rchild_4346_, v_lchild_4348_);
                if crate::leanh::lean_obj_tag(v___x_4409_) == 1 {
                    v_color_4410_ = crate::leanh::lean_ctor_get_uint8(
                        v___x_4409_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 4) as u32,
                    );
                    if v_color_4410_ == 0 {
                        v_lchild_4411_ = crate::leanh::lean_ctor_get(v___x_4409_, 0);
                        v_key_4412_ = crate::leanh::lean_ctor_get(v___x_4409_, 1);
                        v_val_4413_ = crate::leanh::lean_ctor_get(v___x_4409_, 2);
                        v_rchild_4414_ = crate::leanh::lean_ctor_get(v___x_4409_, 3);
                        v_isSharedCheck_4427_ =
                            (!crate::leanh::lean_is_exclusive(v___x_4409_)) as u8;
                        if v_isSharedCheck_4427_ == 0 {
                            v___x_4416_ = v___x_4409_;
                            v_isShared_4417_ = v_isSharedCheck_4427_;
                            state = 13;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_rchild_4414_);
                            crate::leanh::lean_inc(v_val_4413_);
                            crate::leanh::lean_inc(v_key_4412_);
                            crate::leanh::lean_inc(v_lchild_4411_);
                            crate::leanh::lean_dec(v___x_4409_);
                            v___x_4416_ = crate::leanh::lean_box(0);
                            v_isShared_4417_ = v_isSharedCheck_4427_;
                            state = 13;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_del_object(v___x_4407_);
                        crate::leanh::lean_del_object(v___x_4400_);
                        v_bc_4353_ = v___x_4409_;
                        state = 1;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_4407_);
                    crate::leanh::lean_del_object(v___x_4400_);
                    v_bc_4353_ = v___x_4409_;
                    state = 1;
                    continue;
                }
            }
            13 => {
                if v_isShared_4417_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4416_, 3, v_lchild_4411_);
                    crate::leanh::lean_ctor_set(v___x_4416_, 2, v_val_4345_);
                    crate::leanh::lean_ctor_set(v___x_4416_, 1, v_key_4344_);
                    crate::leanh::lean_ctor_set(v___x_4416_, 0, v_lchild_4343_);
                    v___x_4419_ = v___x_4416_;
                    state = 14;
                    continue;
                } else {
                    v_reuseFailAlloc_4426_ = crate::leanh::lean_alloc_ctor(1, 4, (1) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4426_, 0, v_lchild_4343_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4426_, 1, v_key_4344_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4426_, 2, v_val_4345_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4426_, 3, v_lchild_4411_);
                    v___x_4419_ = v_reuseFailAlloc_4426_;
                    state = 14;
                    continue;
                }
            }
            14 => {
                crate::leanh::lean_ctor_set_uint8(
                    v___x_4419_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 4) as u32,
                    v_color_4342_,
                );
                if v_isShared_4408_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4407_, 0, v_rchild_4414_);
                    v___x_4421_ = v___x_4407_;
                    state = 15;
                    continue;
                } else {
                    v_reuseFailAlloc_4425_ = crate::leanh::lean_alloc_ctor(1, 4, (1) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4425_, 0, v_rchild_4414_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4425_, 1, v_key_4349_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4425_, 2, v_val_4350_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4425_, 3, v_rchild_4351_);
                    v___x_4421_ = v_reuseFailAlloc_4425_;
                    state = 15;
                    continue;
                }
            }
            15 => {
                crate::leanh::lean_ctor_set_uint8(
                    v___x_4421_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 4) as u32,
                    v_color_4342_,
                );
                if v_isShared_4401_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4400_, 3, v___x_4421_);
                    crate::leanh::lean_ctor_set(v___x_4400_, 2, v_val_4413_);
                    crate::leanh::lean_ctor_set(v___x_4400_, 1, v_key_4412_);
                    crate::leanh::lean_ctor_set(v___x_4400_, 0, v___x_4419_);
                    v___x_4423_ = v___x_4400_;
                    state = 16;
                    continue;
                } else {
                    v_reuseFailAlloc_4424_ = crate::leanh::lean_alloc_ctor(1, 4, (1) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4424_, 0, v___x_4419_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4424_, 1, v_key_4412_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4424_, 2, v_val_4413_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4424_, 3, v___x_4421_);
                    v___x_4423_ = v_reuseFailAlloc_4424_;
                    state = 16;
                    continue;
                }
            }
            16 => {
                crate::leanh::lean_ctor_set_uint8(
                    v___x_4423_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 4) as u32,
                    v_color_4410_,
                );
                return v___x_4423_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_RBNode_appendTrees(
    mut v_00_u03b1_4438_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_4439_: *mut crate::leanh::LeanObject,
    mut v_x_4440_: *mut crate::leanh::LeanObject,
    mut v_x_4441_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4442_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4442_ = l_Lean_RBNode_appendTrees___redArg(v_x_4440_, v_x_4441_);
    return v___x_4442_;
}
pub unsafe fn l___private_Lean_Data_RBMap_0__Lean_RBNode_appendTrees_match__1_splitter___redArg(
    mut v_x_4443_: *mut crate::leanh::LeanObject,
    mut v_x_4444_: *mut crate::leanh::LeanObject,
    mut v_h__1_4445_: *mut crate::leanh::LeanObject,
    mut v_h__2_4446_: *mut crate::leanh::LeanObject,
    mut v_h__3_4447_: *mut crate::leanh::LeanObject,
    mut v_h__4_4448_: *mut crate::leanh::LeanObject,
    mut v_h__5_4449_: *mut crate::leanh::LeanObject,
    mut v_h__6_4450_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_4443_) == 0 {
        let mut v___x_4451_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__6_4450_);
        crate::leanh::lean_dec(v_h__5_4449_);
        crate::leanh::lean_dec(v_h__4_4448_);
        crate::leanh::lean_dec(v_h__3_4447_);
        crate::leanh::lean_dec(v_h__2_4446_);
        v___x_4451_ = crate::leanh::lean_apply_1(v_h__1_4445_, v_x_4444_);
        return v___x_4451_;
    } else {
        crate::leanh::lean_dec(v_h__1_4445_);
        if crate::leanh::lean_obj_tag(v_x_4444_) == 0 {
            let mut v___x_4452_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__6_4450_);
            crate::leanh::lean_dec(v_h__5_4449_);
            crate::leanh::lean_dec(v_h__4_4448_);
            crate::leanh::lean_dec(v_h__3_4447_);
            v___x_4452_ =
                crate::leanh::lean_apply_2(v_h__2_4446_, v_x_4443_, crate::leanh::lean_box(0));
            return v___x_4452_;
        } else {
            let mut v_color_4453_: u8 = 0;
            crate::leanh::lean_dec(v_h__2_4446_);
            v_color_4453_ = crate::leanh::lean_ctor_get_uint8(
                v_x_4444_,
                (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 4) as u32,
            );
            if v_color_4453_ == 0 {
                let mut v_color_4454_: u8 = 0;
                crate::leanh::lean_dec(v_h__6_4450_);
                crate::leanh::lean_dec(v_h__4_4448_);
                v_color_4454_ = crate::leanh::lean_ctor_get_uint8(
                    v_x_4443_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 4) as u32,
                );
                if v_color_4454_ == 0 {
                    let mut v_lchild_4455_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                    let mut v_key_4456_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                    let mut v_val_4457_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                    let mut v_rchild_4458_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                    let mut v_lchild_4459_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                    let mut v_key_4460_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                    let mut v_val_4461_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                    let mut v_rchild_4462_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                    let mut v___x_4463_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                    crate::leanh::lean_dec(v_h__5_4449_);
                    v_lchild_4455_ = crate::leanh::lean_ctor_get(v_x_4443_, 0);
                    crate::leanh::lean_inc(v_lchild_4455_);
                    v_key_4456_ = crate::leanh::lean_ctor_get(v_x_4443_, 1);
                    crate::leanh::lean_inc(v_key_4456_);
                    v_val_4457_ = crate::leanh::lean_ctor_get(v_x_4443_, 2);
                    crate::leanh::lean_inc(v_val_4457_);
                    v_rchild_4458_ = crate::leanh::lean_ctor_get(v_x_4443_, 3);
                    crate::leanh::lean_inc(v_rchild_4458_);
                    crate::leanh::lean_dec_ref_known(v_x_4443_, 4);
                    v_lchild_4459_ = crate::leanh::lean_ctor_get(v_x_4444_, 0);
                    crate::leanh::lean_inc(v_lchild_4459_);
                    v_key_4460_ = crate::leanh::lean_ctor_get(v_x_4444_, 1);
                    crate::leanh::lean_inc(v_key_4460_);
                    v_val_4461_ = crate::leanh::lean_ctor_get(v_x_4444_, 2);
                    crate::leanh::lean_inc(v_val_4461_);
                    v_rchild_4462_ = crate::leanh::lean_ctor_get(v_x_4444_, 3);
                    crate::leanh::lean_inc(v_rchild_4462_);
                    crate::leanh::lean_dec_ref_known(v_x_4444_, 4);
                    v___x_4463_ = crate::leanh::lean_apply_8(
                        v_h__3_4447_,
                        v_lchild_4455_,
                        v_key_4456_,
                        v_val_4457_,
                        v_rchild_4458_,
                        v_lchild_4459_,
                        v_key_4460_,
                        v_val_4461_,
                        v_rchild_4462_,
                    );
                    return v___x_4463_;
                } else {
                    let mut v_lchild_4464_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                    let mut v_key_4465_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                    let mut v_val_4466_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                    let mut v_rchild_4467_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                    let mut v___x_4468_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                    crate::leanh::lean_dec(v_h__3_4447_);
                    v_lchild_4464_ = crate::leanh::lean_ctor_get(v_x_4444_, 0);
                    crate::leanh::lean_inc(v_lchild_4464_);
                    v_key_4465_ = crate::leanh::lean_ctor_get(v_x_4444_, 1);
                    crate::leanh::lean_inc(v_key_4465_);
                    v_val_4466_ = crate::leanh::lean_ctor_get(v_x_4444_, 2);
                    crate::leanh::lean_inc(v_val_4466_);
                    v_rchild_4467_ = crate::leanh::lean_ctor_get(v_x_4444_, 3);
                    crate::leanh::lean_inc(v_rchild_4467_);
                    crate::leanh::lean_dec_ref_known(v_x_4444_, 4);
                    v___x_4468_ = crate::leanh::lean_apply_7(
                        v_h__5_4449_,
                        v_x_4443_,
                        v_lchild_4464_,
                        v_key_4465_,
                        v_val_4466_,
                        v_rchild_4467_,
                        crate::leanh::lean_box(0),
                        crate::leanh::lean_box(0),
                    );
                    return v___x_4468_;
                }
            } else {
                let mut v_color_4469_: u8 = 0;
                crate::leanh::lean_dec(v_h__5_4449_);
                crate::leanh::lean_dec(v_h__3_4447_);
                v_color_4469_ = crate::leanh::lean_ctor_get_uint8(
                    v_x_4443_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 4) as u32,
                );
                if v_color_4469_ == 0 {
                    let mut v_lchild_4470_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                    let mut v_key_4471_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                    let mut v_val_4472_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                    let mut v_rchild_4473_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                    let mut v___x_4474_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                    crate::leanh::lean_dec(v_h__4_4448_);
                    v_lchild_4470_ = crate::leanh::lean_ctor_get(v_x_4443_, 0);
                    crate::leanh::lean_inc(v_lchild_4470_);
                    v_key_4471_ = crate::leanh::lean_ctor_get(v_x_4443_, 1);
                    crate::leanh::lean_inc(v_key_4471_);
                    v_val_4472_ = crate::leanh::lean_ctor_get(v_x_4443_, 2);
                    crate::leanh::lean_inc(v_val_4472_);
                    v_rchild_4473_ = crate::leanh::lean_ctor_get(v_x_4443_, 3);
                    crate::leanh::lean_inc(v_rchild_4473_);
                    crate::leanh::lean_dec_ref_known(v_x_4443_, 4);
                    v___x_4474_ = crate::leanh::lean_apply_7(
                        v_h__6_4450_,
                        v_lchild_4470_,
                        v_key_4471_,
                        v_val_4472_,
                        v_rchild_4473_,
                        v_x_4444_,
                        crate::leanh::lean_box(0),
                        crate::leanh::lean_box(0),
                    );
                    return v___x_4474_;
                } else {
                    let mut v_lchild_4475_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                    let mut v_key_4476_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                    let mut v_val_4477_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                    let mut v_rchild_4478_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                    let mut v_lchild_4479_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                    let mut v_key_4480_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                    let mut v_val_4481_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                    let mut v_rchild_4482_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                    let mut v___x_4483_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                    crate::leanh::lean_dec(v_h__6_4450_);
                    v_lchild_4475_ = crate::leanh::lean_ctor_get(v_x_4443_, 0);
                    crate::leanh::lean_inc(v_lchild_4475_);
                    v_key_4476_ = crate::leanh::lean_ctor_get(v_x_4443_, 1);
                    crate::leanh::lean_inc(v_key_4476_);
                    v_val_4477_ = crate::leanh::lean_ctor_get(v_x_4443_, 2);
                    crate::leanh::lean_inc(v_val_4477_);
                    v_rchild_4478_ = crate::leanh::lean_ctor_get(v_x_4443_, 3);
                    crate::leanh::lean_inc(v_rchild_4478_);
                    crate::leanh::lean_dec_ref_known(v_x_4443_, 4);
                    v_lchild_4479_ = crate::leanh::lean_ctor_get(v_x_4444_, 0);
                    crate::leanh::lean_inc(v_lchild_4479_);
                    v_key_4480_ = crate::leanh::lean_ctor_get(v_x_4444_, 1);
                    crate::leanh::lean_inc(v_key_4480_);
                    v_val_4481_ = crate::leanh::lean_ctor_get(v_x_4444_, 2);
                    crate::leanh::lean_inc(v_val_4481_);
                    v_rchild_4482_ = crate::leanh::lean_ctor_get(v_x_4444_, 3);
                    crate::leanh::lean_inc(v_rchild_4482_);
                    crate::leanh::lean_dec_ref_known(v_x_4444_, 4);
                    v___x_4483_ = crate::leanh::lean_apply_8(
                        v_h__4_4448_,
                        v_lchild_4475_,
                        v_key_4476_,
                        v_val_4477_,
                        v_rchild_4478_,
                        v_lchild_4479_,
                        v_key_4480_,
                        v_val_4481_,
                        v_rchild_4482_,
                    );
                    return v___x_4483_;
                }
            }
        }
    }
}
pub unsafe fn l___private_Lean_Data_RBMap_0__Lean_RBNode_appendTrees_match__1_splitter(
    mut v_00_u03b1_4484_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_4485_: *mut crate::leanh::LeanObject,
    mut v_motive_4486_: *mut crate::leanh::LeanObject,
    mut v_x_4487_: *mut crate::leanh::LeanObject,
    mut v_x_4488_: *mut crate::leanh::LeanObject,
    mut v_h__1_4489_: *mut crate::leanh::LeanObject,
    mut v_h__2_4490_: *mut crate::leanh::LeanObject,
    mut v_h__3_4491_: *mut crate::leanh::LeanObject,
    mut v_h__4_4492_: *mut crate::leanh::LeanObject,
    mut v_h__5_4493_: *mut crate::leanh::LeanObject,
    mut v_h__6_4494_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_4487_) == 0 {
        let mut v___x_4495_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__6_4494_);
        crate::leanh::lean_dec(v_h__5_4493_);
        crate::leanh::lean_dec(v_h__4_4492_);
        crate::leanh::lean_dec(v_h__3_4491_);
        crate::leanh::lean_dec(v_h__2_4490_);
        v___x_4495_ = crate::leanh::lean_apply_1(v_h__1_4489_, v_x_4488_);
        return v___x_4495_;
    } else {
        crate::leanh::lean_dec(v_h__1_4489_);
        if crate::leanh::lean_obj_tag(v_x_4488_) == 0 {
            let mut v___x_4496_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__6_4494_);
            crate::leanh::lean_dec(v_h__5_4493_);
            crate::leanh::lean_dec(v_h__4_4492_);
            crate::leanh::lean_dec(v_h__3_4491_);
            v___x_4496_ =
                crate::leanh::lean_apply_2(v_h__2_4490_, v_x_4487_, crate::leanh::lean_box(0));
            return v___x_4496_;
        } else {
            let mut v_color_4497_: u8 = 0;
            crate::leanh::lean_dec(v_h__2_4490_);
            v_color_4497_ = crate::leanh::lean_ctor_get_uint8(
                v_x_4488_,
                (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 4) as u32,
            );
            if v_color_4497_ == 0 {
                let mut v_color_4498_: u8 = 0;
                crate::leanh::lean_dec(v_h__6_4494_);
                crate::leanh::lean_dec(v_h__4_4492_);
                v_color_4498_ = crate::leanh::lean_ctor_get_uint8(
                    v_x_4487_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 4) as u32,
                );
                if v_color_4498_ == 0 {
                    let mut v_lchild_4499_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                    let mut v_key_4500_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                    let mut v_val_4501_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                    let mut v_rchild_4502_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                    let mut v_lchild_4503_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                    let mut v_key_4504_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                    let mut v_val_4505_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                    let mut v_rchild_4506_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                    let mut v___x_4507_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                    crate::leanh::lean_dec(v_h__5_4493_);
                    v_lchild_4499_ = crate::leanh::lean_ctor_get(v_x_4487_, 0);
                    crate::leanh::lean_inc(v_lchild_4499_);
                    v_key_4500_ = crate::leanh::lean_ctor_get(v_x_4487_, 1);
                    crate::leanh::lean_inc(v_key_4500_);
                    v_val_4501_ = crate::leanh::lean_ctor_get(v_x_4487_, 2);
                    crate::leanh::lean_inc(v_val_4501_);
                    v_rchild_4502_ = crate::leanh::lean_ctor_get(v_x_4487_, 3);
                    crate::leanh::lean_inc(v_rchild_4502_);
                    crate::leanh::lean_dec_ref_known(v_x_4487_, 4);
                    v_lchild_4503_ = crate::leanh::lean_ctor_get(v_x_4488_, 0);
                    crate::leanh::lean_inc(v_lchild_4503_);
                    v_key_4504_ = crate::leanh::lean_ctor_get(v_x_4488_, 1);
                    crate::leanh::lean_inc(v_key_4504_);
                    v_val_4505_ = crate::leanh::lean_ctor_get(v_x_4488_, 2);
                    crate::leanh::lean_inc(v_val_4505_);
                    v_rchild_4506_ = crate::leanh::lean_ctor_get(v_x_4488_, 3);
                    crate::leanh::lean_inc(v_rchild_4506_);
                    crate::leanh::lean_dec_ref_known(v_x_4488_, 4);
                    v___x_4507_ = crate::leanh::lean_apply_8(
                        v_h__3_4491_,
                        v_lchild_4499_,
                        v_key_4500_,
                        v_val_4501_,
                        v_rchild_4502_,
                        v_lchild_4503_,
                        v_key_4504_,
                        v_val_4505_,
                        v_rchild_4506_,
                    );
                    return v___x_4507_;
                } else {
                    let mut v_lchild_4508_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                    let mut v_key_4509_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                    let mut v_val_4510_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                    let mut v_rchild_4511_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                    let mut v___x_4512_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                    crate::leanh::lean_dec(v_h__3_4491_);
                    v_lchild_4508_ = crate::leanh::lean_ctor_get(v_x_4488_, 0);
                    crate::leanh::lean_inc(v_lchild_4508_);
                    v_key_4509_ = crate::leanh::lean_ctor_get(v_x_4488_, 1);
                    crate::leanh::lean_inc(v_key_4509_);
                    v_val_4510_ = crate::leanh::lean_ctor_get(v_x_4488_, 2);
                    crate::leanh::lean_inc(v_val_4510_);
                    v_rchild_4511_ = crate::leanh::lean_ctor_get(v_x_4488_, 3);
                    crate::leanh::lean_inc(v_rchild_4511_);
                    crate::leanh::lean_dec_ref_known(v_x_4488_, 4);
                    v___x_4512_ = crate::leanh::lean_apply_7(
                        v_h__5_4493_,
                        v_x_4487_,
                        v_lchild_4508_,
                        v_key_4509_,
                        v_val_4510_,
                        v_rchild_4511_,
                        crate::leanh::lean_box(0),
                        crate::leanh::lean_box(0),
                    );
                    return v___x_4512_;
                }
            } else {
                let mut v_color_4513_: u8 = 0;
                crate::leanh::lean_dec(v_h__5_4493_);
                crate::leanh::lean_dec(v_h__3_4491_);
                v_color_4513_ = crate::leanh::lean_ctor_get_uint8(
                    v_x_4487_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 4) as u32,
                );
                if v_color_4513_ == 0 {
                    let mut v_lchild_4514_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                    let mut v_key_4515_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                    let mut v_val_4516_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                    let mut v_rchild_4517_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                    let mut v___x_4518_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                    crate::leanh::lean_dec(v_h__4_4492_);
                    v_lchild_4514_ = crate::leanh::lean_ctor_get(v_x_4487_, 0);
                    crate::leanh::lean_inc(v_lchild_4514_);
                    v_key_4515_ = crate::leanh::lean_ctor_get(v_x_4487_, 1);
                    crate::leanh::lean_inc(v_key_4515_);
                    v_val_4516_ = crate::leanh::lean_ctor_get(v_x_4487_, 2);
                    crate::leanh::lean_inc(v_val_4516_);
                    v_rchild_4517_ = crate::leanh::lean_ctor_get(v_x_4487_, 3);
                    crate::leanh::lean_inc(v_rchild_4517_);
                    crate::leanh::lean_dec_ref_known(v_x_4487_, 4);
                    v___x_4518_ = crate::leanh::lean_apply_7(
                        v_h__6_4494_,
                        v_lchild_4514_,
                        v_key_4515_,
                        v_val_4516_,
                        v_rchild_4517_,
                        v_x_4488_,
                        crate::leanh::lean_box(0),
                        crate::leanh::lean_box(0),
                    );
                    return v___x_4518_;
                } else {
                    let mut v_lchild_4519_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                    let mut v_key_4520_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                    let mut v_val_4521_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                    let mut v_rchild_4522_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                    let mut v_lchild_4523_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                    let mut v_key_4524_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                    let mut v_val_4525_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                    let mut v_rchild_4526_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                    let mut v___x_4527_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                    crate::leanh::lean_dec(v_h__6_4494_);
                    v_lchild_4519_ = crate::leanh::lean_ctor_get(v_x_4487_, 0);
                    crate::leanh::lean_inc(v_lchild_4519_);
                    v_key_4520_ = crate::leanh::lean_ctor_get(v_x_4487_, 1);
                    crate::leanh::lean_inc(v_key_4520_);
                    v_val_4521_ = crate::leanh::lean_ctor_get(v_x_4487_, 2);
                    crate::leanh::lean_inc(v_val_4521_);
                    v_rchild_4522_ = crate::leanh::lean_ctor_get(v_x_4487_, 3);
                    crate::leanh::lean_inc(v_rchild_4522_);
                    crate::leanh::lean_dec_ref_known(v_x_4487_, 4);
                    v_lchild_4523_ = crate::leanh::lean_ctor_get(v_x_4488_, 0);
                    crate::leanh::lean_inc(v_lchild_4523_);
                    v_key_4524_ = crate::leanh::lean_ctor_get(v_x_4488_, 1);
                    crate::leanh::lean_inc(v_key_4524_);
                    v_val_4525_ = crate::leanh::lean_ctor_get(v_x_4488_, 2);
                    crate::leanh::lean_inc(v_val_4525_);
                    v_rchild_4526_ = crate::leanh::lean_ctor_get(v_x_4488_, 3);
                    crate::leanh::lean_inc(v_rchild_4526_);
                    crate::leanh::lean_dec_ref_known(v_x_4488_, 4);
                    v___x_4527_ = crate::leanh::lean_apply_8(
                        v_h__4_4492_,
                        v_lchild_4519_,
                        v_key_4520_,
                        v_val_4521_,
                        v_rchild_4522_,
                        v_lchild_4523_,
                        v_key_4524_,
                        v_val_4525_,
                        v_rchild_4526_,
                    );
                    return v___x_4527_;
                }
            }
        }
    }
}
pub unsafe fn l___private_Lean_Data_RBMap_0__Lean_RBNode_isRed_match__1_splitter___redArg(
    mut v_x_4528_: *mut crate::leanh::LeanObject,
    mut v_h__1_4529_: *mut crate::leanh::LeanObject,
    mut v_h__2_4530_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_4528_) == 1 {
        let mut v_color_4531_: u8 = 0;
        v_color_4531_ = crate::leanh::lean_ctor_get_uint8(
            v_x_4528_,
            (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 4) as u32,
        );
        if v_color_4531_ == 0 {
            let mut v_lchild_4532_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_key_4533_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_val_4534_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_rchild_4535_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_4536_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__2_4530_);
            v_lchild_4532_ = crate::leanh::lean_ctor_get(v_x_4528_, 0);
            crate::leanh::lean_inc(v_lchild_4532_);
            v_key_4533_ = crate::leanh::lean_ctor_get(v_x_4528_, 1);
            crate::leanh::lean_inc(v_key_4533_);
            v_val_4534_ = crate::leanh::lean_ctor_get(v_x_4528_, 2);
            crate::leanh::lean_inc(v_val_4534_);
            v_rchild_4535_ = crate::leanh::lean_ctor_get(v_x_4528_, 3);
            crate::leanh::lean_inc(v_rchild_4535_);
            crate::leanh::lean_dec_ref_known(v_x_4528_, 4);
            v___x_4536_ = crate::leanh::lean_apply_4(
                v_h__1_4529_,
                v_lchild_4532_,
                v_key_4533_,
                v_val_4534_,
                v_rchild_4535_,
            );
            return v___x_4536_;
        } else {
            let mut v___x_4537_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__1_4529_);
            v___x_4537_ =
                crate::leanh::lean_apply_2(v_h__2_4530_, v_x_4528_, crate::leanh::lean_box(0));
            return v___x_4537_;
        }
    } else {
        let mut v___x_4538_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_4529_);
        v___x_4538_ =
            crate::leanh::lean_apply_2(v_h__2_4530_, v_x_4528_, crate::leanh::lean_box(0));
        return v___x_4538_;
    }
}
pub unsafe fn l___private_Lean_Data_RBMap_0__Lean_RBNode_isRed_match__1_splitter(
    mut v_00_u03b1_4539_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_4540_: *mut crate::leanh::LeanObject,
    mut v_motive_4541_: *mut crate::leanh::LeanObject,
    mut v_x_4542_: *mut crate::leanh::LeanObject,
    mut v_h__1_4543_: *mut crate::leanh::LeanObject,
    mut v_h__2_4544_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_4542_) == 1 {
        let mut v_color_4545_: u8 = 0;
        v_color_4545_ = crate::leanh::lean_ctor_get_uint8(
            v_x_4542_,
            (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 4) as u32,
        );
        if v_color_4545_ == 0 {
            let mut v_lchild_4546_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_key_4547_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_val_4548_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_rchild_4549_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_4550_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__2_4544_);
            v_lchild_4546_ = crate::leanh::lean_ctor_get(v_x_4542_, 0);
            crate::leanh::lean_inc(v_lchild_4546_);
            v_key_4547_ = crate::leanh::lean_ctor_get(v_x_4542_, 1);
            crate::leanh::lean_inc(v_key_4547_);
            v_val_4548_ = crate::leanh::lean_ctor_get(v_x_4542_, 2);
            crate::leanh::lean_inc(v_val_4548_);
            v_rchild_4549_ = crate::leanh::lean_ctor_get(v_x_4542_, 3);
            crate::leanh::lean_inc(v_rchild_4549_);
            crate::leanh::lean_dec_ref_known(v_x_4542_, 4);
            v___x_4550_ = crate::leanh::lean_apply_4(
                v_h__1_4543_,
                v_lchild_4546_,
                v_key_4547_,
                v_val_4548_,
                v_rchild_4549_,
            );
            return v___x_4550_;
        } else {
            let mut v___x_4551_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__1_4543_);
            v___x_4551_ =
                crate::leanh::lean_apply_2(v_h__2_4544_, v_x_4542_, crate::leanh::lean_box(0));
            return v___x_4551_;
        }
    } else {
        let mut v___x_4552_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_4543_);
        v___x_4552_ =
            crate::leanh::lean_apply_2(v_h__2_4544_, v_x_4542_, crate::leanh::lean_box(0));
        return v___x_4552_;
    }
}
pub unsafe fn l_Lean_RBNode_del___redArg(
    mut v_cmp_4553_: *mut crate::leanh::LeanObject,
    mut v_x_4554_: *mut crate::leanh::LeanObject,
    mut v_x_4555_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_lchild_4556_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_key_4557_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_4558_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_rchild_4559_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4561_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4562_: u8 = 0;
    let mut v___x_4563_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4564_: u8 = 0;
    let mut v___x_4565_: u8 = 0;
    let mut v___x_4566_: u8 = 0;
    let mut v___x_4567_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4569_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4570_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4571_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4572_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4573_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4574_: u8 = 0;
    let mut v___x_4575_: u8 = 0;
    let mut v___x_4576_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4578_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4579_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4580_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4581_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4582_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_4555_) == 0 {
                    crate::leanh::lean_dec(v_x_4554_);
                    crate::leanh::lean_dec_ref(v_cmp_4553_);
                    return v_x_4555_;
                } else {
                    v_lchild_4556_ = crate::leanh::lean_ctor_get(v_x_4555_, 0);
                    v_key_4557_ = crate::leanh::lean_ctor_get(v_x_4555_, 1);
                    v_val_4558_ = crate::leanh::lean_ctor_get(v_x_4555_, 2);
                    v_rchild_4559_ = crate::leanh::lean_ctor_get(v_x_4555_, 3);
                    v_isSharedCheck_4582_ = (!crate::leanh::lean_is_exclusive(v_x_4555_)) as u8;
                    if v_isSharedCheck_4582_ == 0 {
                        v___x_4561_ = v_x_4555_;
                        v_isShared_4562_ = v_isSharedCheck_4582_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_rchild_4559_);
                        crate::leanh::lean_inc(v_val_4558_);
                        crate::leanh::lean_inc(v_key_4557_);
                        crate::leanh::lean_inc(v_lchild_4556_);
                        crate::leanh::lean_dec(v_x_4555_);
                        v___x_4561_ = crate::leanh::lean_box(0);
                        v_isShared_4562_ = v_isSharedCheck_4582_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                crate::leanh::lean_inc_ref(v_cmp_4553_);
                crate::leanh::lean_inc(v_key_4557_);
                crate::leanh::lean_inc(v_x_4554_);
                v___x_4563_ = crate::leanh::lean_apply_2(v_cmp_4553_, v_x_4554_, v_key_4557_);
                v___x_4564_ = (crate::leanh::lean_unbox(v___x_4563_) as u8);
                match v___x_4564_ {
                    0 => {
                        v___x_4565_ = l_Lean_RBNode_isBlack___redArg(v_lchild_4556_);
                        if v___x_4565_ == 0 {
                            v___x_4566_ = 0;
                            v___x_4567_ =
                                l_Lean_RBNode_del___redArg(v_cmp_4553_, v_x_4554_, v_lchild_4556_);
                            if v_isShared_4562_ == 0 {
                                crate::leanh::lean_ctor_set(v___x_4561_, 0, v___x_4567_);
                                v___x_4569_ = v___x_4561_;
                                state = 2;
                                continue;
                            } else {
                                v_reuseFailAlloc_4570_ =
                                    crate::leanh::lean_alloc_ctor(1, 4, (1) as u32);
                                crate::leanh::lean_ctor_set(v_reuseFailAlloc_4570_, 0, v___x_4567_);
                                crate::leanh::lean_ctor_set(v_reuseFailAlloc_4570_, 1, v_key_4557_);
                                crate::leanh::lean_ctor_set(v_reuseFailAlloc_4570_, 2, v_val_4558_);
                                crate::leanh::lean_ctor_set(
                                    v_reuseFailAlloc_4570_,
                                    3,
                                    v_rchild_4559_,
                                );
                                v___x_4569_ = v_reuseFailAlloc_4570_;
                                state = 2;
                                continue;
                            }
                        } else {
                            crate::leanh::lean_del_object(v___x_4561_);
                            v___x_4571_ =
                                l_Lean_RBNode_del___redArg(v_cmp_4553_, v_x_4554_, v_lchild_4556_);
                            v___x_4572_ = l_Lean_RBNode_balLeft___redArg(
                                v___x_4571_,
                                v_key_4557_,
                                v_val_4558_,
                                v_rchild_4559_,
                            );
                            return v___x_4572_;
                        }
                    }
                    1 => {
                        crate::leanh::lean_del_object(v___x_4561_);
                        crate::leanh::lean_dec(v_val_4558_);
                        crate::leanh::lean_dec(v_key_4557_);
                        crate::leanh::lean_dec(v_x_4554_);
                        crate::leanh::lean_dec_ref(v_cmp_4553_);
                        v___x_4573_ =
                            l_Lean_RBNode_appendTrees___redArg(v_lchild_4556_, v_rchild_4559_);
                        return v___x_4573_;
                    }
                    _ => {
                        v___x_4574_ = l_Lean_RBNode_isBlack___redArg(v_rchild_4559_);
                        if v___x_4574_ == 0 {
                            v___x_4575_ = 0;
                            v___x_4576_ =
                                l_Lean_RBNode_del___redArg(v_cmp_4553_, v_x_4554_, v_rchild_4559_);
                            if v_isShared_4562_ == 0 {
                                crate::leanh::lean_ctor_set(v___x_4561_, 3, v___x_4576_);
                                v___x_4578_ = v___x_4561_;
                                state = 3;
                                continue;
                            } else {
                                v_reuseFailAlloc_4579_ =
                                    crate::leanh::lean_alloc_ctor(1, 4, (1) as u32);
                                crate::leanh::lean_ctor_set(
                                    v_reuseFailAlloc_4579_,
                                    0,
                                    v_lchild_4556_,
                                );
                                crate::leanh::lean_ctor_set(v_reuseFailAlloc_4579_, 1, v_key_4557_);
                                crate::leanh::lean_ctor_set(v_reuseFailAlloc_4579_, 2, v_val_4558_);
                                crate::leanh::lean_ctor_set(v_reuseFailAlloc_4579_, 3, v___x_4576_);
                                v___x_4578_ = v_reuseFailAlloc_4579_;
                                state = 3;
                                continue;
                            }
                        } else {
                            crate::leanh::lean_del_object(v___x_4561_);
                            v___x_4580_ =
                                l_Lean_RBNode_del___redArg(v_cmp_4553_, v_x_4554_, v_rchild_4559_);
                            v___x_4581_ = l_Lean_RBNode_balRight___redArg(
                                v_lchild_4556_,
                                v_key_4557_,
                                v_val_4558_,
                                v___x_4580_,
                            );
                            return v___x_4581_;
                        }
                    }
                }
            }
            2 => {
                crate::leanh::lean_ctor_set_uint8(
                    v___x_4569_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 4) as u32,
                    v___x_4566_,
                );
                return v___x_4569_;
            }
            3 => {
                crate::leanh::lean_ctor_set_uint8(
                    v___x_4578_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 4) as u32,
                    v___x_4575_,
                );
                return v___x_4578_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_RBNode_del(
    mut v_00_u03b1_4583_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_4584_: *mut crate::leanh::LeanObject,
    mut v_cmp_4585_: *mut crate::leanh::LeanObject,
    mut v_x_4586_: *mut crate::leanh::LeanObject,
    mut v_x_4587_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4588_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4588_ = l_Lean_RBNode_del___redArg(v_cmp_4585_, v_x_4586_, v_x_4587_);
    return v___x_4588_;
}
pub unsafe fn l_Lean_RBNode_erase___redArg(
    mut v_cmp_4589_: *mut crate::leanh::LeanObject,
    mut v_x_4590_: *mut crate::leanh::LeanObject,
    mut v_t_4591_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_t_4592_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4593_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_t_4592_ = l_Lean_RBNode_del___redArg(v_cmp_4589_, v_x_4590_, v_t_4591_);
    v___x_4593_ = l_Lean_RBNode_setBlack___redArg(v_t_4592_);
    return v___x_4593_;
}
pub unsafe fn l_Lean_RBNode_erase(
    mut v_00_u03b1_4594_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_4595_: *mut crate::leanh::LeanObject,
    mut v_cmp_4596_: *mut crate::leanh::LeanObject,
    mut v_x_4597_: *mut crate::leanh::LeanObject,
    mut v_t_4598_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4599_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4599_ = l_Lean_RBNode_erase___redArg(v_cmp_4596_, v_x_4597_, v_t_4598_);
    return v___x_4599_;
}
pub unsafe fn l_Lean_RBNode_findCore___redArg(
    mut v_cmp_4600_: *mut crate::leanh::LeanObject,
    mut v_x_4601_: *mut crate::leanh::LeanObject,
    mut v_x_4602_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4603_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_lchild_4604_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_key_4605_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_4606_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_rchild_4607_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4608_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4609_: u8 = 0;
    let mut v___x_4611_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4612_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_4601_) == 0 {
                    crate::leanh::lean_dec(v_x_4602_);
                    crate::leanh::lean_dec_ref(v_cmp_4600_);
                    v___x_4603_ = crate::leanh::lean_box(0);
                    return v___x_4603_;
                } else {
                    v_lchild_4604_ = crate::leanh::lean_ctor_get(v_x_4601_, 0);
                    crate::leanh::lean_inc(v_lchild_4604_);
                    v_key_4605_ = crate::leanh::lean_ctor_get(v_x_4601_, 1);
                    crate::leanh::lean_inc_n(v_key_4605_, 2);
                    v_val_4606_ = crate::leanh::lean_ctor_get(v_x_4601_, 2);
                    crate::leanh::lean_inc(v_val_4606_);
                    v_rchild_4607_ = crate::leanh::lean_ctor_get(v_x_4601_, 3);
                    crate::leanh::lean_inc(v_rchild_4607_);
                    crate::leanh::lean_dec_ref_known(v_x_4601_, 4);
                    crate::leanh::lean_inc_ref(v_cmp_4600_);
                    crate::leanh::lean_inc(v_x_4602_);
                    v___x_4608_ = crate::leanh::lean_apply_2(v_cmp_4600_, v_x_4602_, v_key_4605_);
                    v___x_4609_ = (crate::leanh::lean_unbox(v___x_4608_) as u8);
                    match v___x_4609_ {
                        0 => {
                            crate::leanh::lean_dec(v_rchild_4607_);
                            crate::leanh::lean_dec(v_val_4606_);
                            crate::leanh::lean_dec(v_key_4605_);
                            v_x_4601_ = v_lchild_4604_;
                            state = 0;
                            continue;
                        }
                        1 => {
                            crate::leanh::lean_dec(v_rchild_4607_);
                            crate::leanh::lean_dec(v_lchild_4604_);
                            crate::leanh::lean_dec(v_x_4602_);
                            crate::leanh::lean_dec_ref(v_cmp_4600_);
                            v___x_4611_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(v___x_4611_, 0, v_key_4605_);
                            crate::leanh::lean_ctor_set(v___x_4611_, 1, v_val_4606_);
                            v___x_4612_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                            crate::leanh::lean_ctor_set(v___x_4612_, 0, v___x_4611_);
                            return v___x_4612_;
                        }
                        _ => {
                            crate::leanh::lean_dec(v_val_4606_);
                            crate::leanh::lean_dec(v_key_4605_);
                            crate::leanh::lean_dec(v_lchild_4604_);
                            v_x_4601_ = v_rchild_4607_;
                            state = 0;
                            continue;
                        }
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_RBNode_findCore(
    mut v_00_u03b1_4614_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_4615_: *mut crate::leanh::LeanObject,
    mut v_cmp_4616_: *mut crate::leanh::LeanObject,
    mut v_x_4617_: *mut crate::leanh::LeanObject,
    mut v_x_4618_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4619_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4619_ = l_Lean_RBNode_findCore___redArg(v_cmp_4616_, v_x_4617_, v_x_4618_);
    return v___x_4619_;
}
pub unsafe fn l_Lean_RBNode_find___redArg(
    mut v_cmp_4620_: *mut crate::leanh::LeanObject,
    mut v_x_4621_: *mut crate::leanh::LeanObject,
    mut v_x_4622_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4623_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_lchild_4624_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_key_4625_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_4626_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_rchild_4627_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4628_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4629_: u8 = 0;
    let mut v___x_4631_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_4621_) == 0 {
                    crate::leanh::lean_dec(v_x_4622_);
                    crate::leanh::lean_dec_ref(v_cmp_4620_);
                    v___x_4623_ = crate::leanh::lean_box(0);
                    return v___x_4623_;
                } else {
                    v_lchild_4624_ = crate::leanh::lean_ctor_get(v_x_4621_, 0);
                    crate::leanh::lean_inc(v_lchild_4624_);
                    v_key_4625_ = crate::leanh::lean_ctor_get(v_x_4621_, 1);
                    crate::leanh::lean_inc(v_key_4625_);
                    v_val_4626_ = crate::leanh::lean_ctor_get(v_x_4621_, 2);
                    crate::leanh::lean_inc(v_val_4626_);
                    v_rchild_4627_ = crate::leanh::lean_ctor_get(v_x_4621_, 3);
                    crate::leanh::lean_inc(v_rchild_4627_);
                    crate::leanh::lean_dec_ref_known(v_x_4621_, 4);
                    crate::leanh::lean_inc_ref(v_cmp_4620_);
                    crate::leanh::lean_inc(v_x_4622_);
                    v___x_4628_ = crate::leanh::lean_apply_2(v_cmp_4620_, v_x_4622_, v_key_4625_);
                    v___x_4629_ = (crate::leanh::lean_unbox(v___x_4628_) as u8);
                    match v___x_4629_ {
                        0 => {
                            crate::leanh::lean_dec(v_rchild_4627_);
                            crate::leanh::lean_dec(v_val_4626_);
                            v_x_4621_ = v_lchild_4624_;
                            state = 0;
                            continue;
                        }
                        1 => {
                            crate::leanh::lean_dec(v_rchild_4627_);
                            crate::leanh::lean_dec(v_lchild_4624_);
                            crate::leanh::lean_dec(v_x_4622_);
                            crate::leanh::lean_dec_ref(v_cmp_4620_);
                            v___x_4631_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                            crate::leanh::lean_ctor_set(v___x_4631_, 0, v_val_4626_);
                            return v___x_4631_;
                        }
                        _ => {
                            crate::leanh::lean_dec(v_val_4626_);
                            crate::leanh::lean_dec(v_lchild_4624_);
                            v_x_4621_ = v_rchild_4627_;
                            state = 0;
                            continue;
                        }
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_RBNode_find(
    mut v_00_u03b1_4633_: *mut crate::leanh::LeanObject,
    mut v_cmp_4634_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_4635_: *mut crate::leanh::LeanObject,
    mut v_x_4636_: *mut crate::leanh::LeanObject,
    mut v_x_4637_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4638_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4638_ = l_Lean_RBNode_find___redArg(v_cmp_4634_, v_x_4636_, v_x_4637_);
    return v___x_4638_;
}
pub unsafe fn l_Lean_RBNode_lowerBound___redArg(
    mut v_cmp_4639_: *mut crate::leanh::LeanObject,
    mut v_x_4640_: *mut crate::leanh::LeanObject,
    mut v_x_4641_: *mut crate::leanh::LeanObject,
    mut v_x_4642_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_lchild_4643_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_key_4644_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_4645_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_rchild_4646_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4647_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4648_: u8 = 0;
    let mut v___x_4650_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4651_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4652_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4653_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_4640_) == 0 {
                    crate::leanh::lean_dec(v_x_4641_);
                    crate::leanh::lean_dec_ref(v_cmp_4639_);
                    return v_x_4642_;
                } else {
                    v_lchild_4643_ = crate::leanh::lean_ctor_get(v_x_4640_, 0);
                    crate::leanh::lean_inc(v_lchild_4643_);
                    v_key_4644_ = crate::leanh::lean_ctor_get(v_x_4640_, 1);
                    crate::leanh::lean_inc_n(v_key_4644_, 2);
                    v_val_4645_ = crate::leanh::lean_ctor_get(v_x_4640_, 2);
                    crate::leanh::lean_inc(v_val_4645_);
                    v_rchild_4646_ = crate::leanh::lean_ctor_get(v_x_4640_, 3);
                    crate::leanh::lean_inc(v_rchild_4646_);
                    crate::leanh::lean_dec_ref_known(v_x_4640_, 4);
                    crate::leanh::lean_inc_ref(v_cmp_4639_);
                    crate::leanh::lean_inc(v_x_4641_);
                    v___x_4647_ = crate::leanh::lean_apply_2(v_cmp_4639_, v_x_4641_, v_key_4644_);
                    v___x_4648_ = (crate::leanh::lean_unbox(v___x_4647_) as u8);
                    match v___x_4648_ {
                        0 => {
                            crate::leanh::lean_dec(v_rchild_4646_);
                            crate::leanh::lean_dec(v_val_4645_);
                            crate::leanh::lean_dec(v_key_4644_);
                            v_x_4640_ = v_lchild_4643_;
                            state = 0;
                            continue;
                        }
                        1 => {
                            crate::leanh::lean_dec(v_rchild_4646_);
                            crate::leanh::lean_dec(v_lchild_4643_);
                            crate::leanh::lean_dec(v_x_4642_);
                            crate::leanh::lean_dec(v_x_4641_);
                            crate::leanh::lean_dec_ref(v_cmp_4639_);
                            v___x_4650_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(v___x_4650_, 0, v_key_4644_);
                            crate::leanh::lean_ctor_set(v___x_4650_, 1, v_val_4645_);
                            v___x_4651_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                            crate::leanh::lean_ctor_set(v___x_4651_, 0, v___x_4650_);
                            return v___x_4651_;
                        }
                        _ => {
                            crate::leanh::lean_dec(v_lchild_4643_);
                            crate::leanh::lean_dec(v_x_4642_);
                            v___x_4652_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(v___x_4652_, 0, v_key_4644_);
                            crate::leanh::lean_ctor_set(v___x_4652_, 1, v_val_4645_);
                            v___x_4653_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                            crate::leanh::lean_ctor_set(v___x_4653_, 0, v___x_4652_);
                            v_x_4640_ = v_rchild_4646_;
                            v_x_4642_ = v___x_4653_;
                            state = 0;
                            continue;
                        }
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_RBNode_lowerBound(
    mut v_00_u03b1_4655_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_4656_: *mut crate::leanh::LeanObject,
    mut v_cmp_4657_: *mut crate::leanh::LeanObject,
    mut v_x_4658_: *mut crate::leanh::LeanObject,
    mut v_x_4659_: *mut crate::leanh::LeanObject,
    mut v_x_4660_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4661_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4661_ = l_Lean_RBNode_lowerBound___redArg(v_cmp_4657_, v_x_4658_, v_x_4659_, v_x_4660_);
    return v___x_4661_;
}
pub unsafe fn l_Lean_RBNode_mapM___redArg___lam__3(
    mut v_color_4662_: u8,
    mut v_key_4663_: *mut crate::leanh::LeanObject,
    mut v_x1_4664_: *mut crate::leanh::LeanObject,
    mut v_x2_4665_: *mut crate::leanh::LeanObject,
    mut v_x3_4666_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4667_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4667_ = crate::leanh::lean_alloc_ctor(1, 4, (1) as u32);
    crate::leanh::lean_ctor_set(v___x_4667_, 0, v_x1_4664_);
    crate::leanh::lean_ctor_set(v___x_4667_, 1, v_key_4663_);
    crate::leanh::lean_ctor_set(v___x_4667_, 2, v_x2_4665_);
    crate::leanh::lean_ctor_set(v___x_4667_, 3, v_x3_4666_);
    crate::leanh::lean_ctor_set_uint8(
        v___x_4667_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 4) as u32,
        v_color_4662_,
    );
    return v___x_4667_;
}
pub unsafe fn l_Lean_RBNode_mapM___redArg___lam__3___boxed(
    mut v_color_4668_: *mut crate::leanh::LeanObject,
    mut v_key_4669_: *mut crate::leanh::LeanObject,
    mut v_x1_4670_: *mut crate::leanh::LeanObject,
    mut v_x2_4671_: *mut crate::leanh::LeanObject,
    mut v_x3_4672_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_color_88__boxed_4673_: u8 = 0;
    let mut v_res_4674_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_color_88__boxed_4673_ = (crate::leanh::lean_unbox(v_color_4668_) as u8);
    v_res_4674_ = l_Lean_RBNode_mapM___redArg___lam__3(
        v_color_88__boxed_4673_,
        v_key_4669_,
        v_x1_4670_,
        v_x2_4671_,
        v_x3_4672_,
    );
    return v_res_4674_;
}
pub unsafe fn l_Lean_RBNode_mapM___redArg___lam__1(
    mut v_f_4675_: *mut crate::leanh::LeanObject,
    mut v_key_4676_: *mut crate::leanh::LeanObject,
    mut v_val_4677_: *mut crate::leanh::LeanObject,
    mut v_x_4678_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4679_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4679_ = crate::leanh::lean_apply_2(v_f_4675_, v_key_4676_, v_val_4677_);
    return v___x_4679_;
}
pub unsafe fn l_Lean_RBNode_mapM___redArg___lam__2(
    mut v_inst_4680_: *mut crate::leanh::LeanObject,
    mut v_f_4681_: *mut crate::leanh::LeanObject,
    mut v_lchild_4682_: *mut crate::leanh::LeanObject,
    mut v_x_4683_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4684_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4684_ = l_Lean_RBNode_mapM___redArg(v_inst_4680_, v_f_4681_, v_lchild_4682_);
    return v___x_4684_;
}
pub unsafe fn l_Lean_RBNode_mapM___redArg(
    mut v_inst_4685_: *mut crate::leanh::LeanObject,
    mut v_f_4686_: *mut crate::leanh::LeanObject,
    mut v_x_4687_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_4687_) == 0 {
        let mut v_toPure_4688_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4689_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4690_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_f_4686_);
        v_toPure_4688_ = crate::leanh::lean_ctor_get(v_inst_4685_, 1);
        crate::leanh::lean_inc(v_toPure_4688_);
        crate::leanh::lean_dec_ref(v_inst_4685_);
        v___x_4689_ = crate::leanh::lean_box(0);
        v___x_4690_ =
            crate::leanh::lean_apply_2(v_toPure_4688_, crate::leanh::lean_box(0), v___x_4689_);
        return v___x_4690_;
    } else {
        let mut v_toPure_4691_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_toSeq_4692_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_color_4693_: u8 = 0;
        let mut v_lchild_4694_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_key_4695_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_val_4696_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_rchild_4697_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___f_4698_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___f_4699_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___f_4700_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4701_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___f_4702_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4703_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4704_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4705_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4706_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_toPure_4691_ = crate::leanh::lean_ctor_get(v_inst_4685_, 1);
        crate::leanh::lean_inc(v_toPure_4691_);
        v_toSeq_4692_ = crate::leanh::lean_ctor_get(v_inst_4685_, 2);
        crate::leanh::lean_inc_n(v_toSeq_4692_, 3);
        v_color_4693_ = crate::leanh::lean_ctor_get_uint8(
            v_x_4687_,
            (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 4) as u32,
        );
        v_lchild_4694_ = crate::leanh::lean_ctor_get(v_x_4687_, 0);
        crate::leanh::lean_inc(v_lchild_4694_);
        v_key_4695_ = crate::leanh::lean_ctor_get(v_x_4687_, 1);
        crate::leanh::lean_inc_n(v_key_4695_, 2);
        v_val_4696_ = crate::leanh::lean_ctor_get(v_x_4687_, 2);
        crate::leanh::lean_inc(v_val_4696_);
        v_rchild_4697_ = crate::leanh::lean_ctor_get(v_x_4687_, 3);
        crate::leanh::lean_inc(v_rchild_4697_);
        crate::leanh::lean_dec_ref_known(v_x_4687_, 4);
        crate::leanh::lean_inc_n(v_f_4686_, 2);
        crate::leanh::lean_inc_ref(v_inst_4685_);
        v___f_4698_ = crate::leanh::lean_alloc_closure(
            l_Lean_RBNode_mapM___redArg___lam__0 as *mut core::ffi::c_void,
            4,
            3,
        );
        crate::leanh::lean_closure_set(v___f_4698_, 0, v_inst_4685_);
        crate::leanh::lean_closure_set(v___f_4698_, 1, v_f_4686_);
        crate::leanh::lean_closure_set(v___f_4698_, 2, v_rchild_4697_);
        v___f_4699_ = crate::leanh::lean_alloc_closure(
            l_Lean_RBNode_mapM___redArg___lam__1 as *mut core::ffi::c_void,
            4,
            3,
        );
        crate::leanh::lean_closure_set(v___f_4699_, 0, v_f_4686_);
        crate::leanh::lean_closure_set(v___f_4699_, 1, v_key_4695_);
        crate::leanh::lean_closure_set(v___f_4699_, 2, v_val_4696_);
        v___f_4700_ = crate::leanh::lean_alloc_closure(
            l_Lean_RBNode_mapM___redArg___lam__2 as *mut core::ffi::c_void,
            4,
            3,
        );
        crate::leanh::lean_closure_set(v___f_4700_, 0, v_inst_4685_);
        crate::leanh::lean_closure_set(v___f_4700_, 1, v_f_4686_);
        crate::leanh::lean_closure_set(v___f_4700_, 2, v_lchild_4694_);
        v___x_4701_ = crate::leanh::lean_box((v_color_4693_) as usize);
        v___f_4702_ = crate::leanh::lean_alloc_closure(
            l_Lean_RBNode_mapM___redArg___lam__3___boxed as *mut core::ffi::c_void,
            5,
            2,
        );
        crate::leanh::lean_closure_set(v___f_4702_, 0, v___x_4701_);
        crate::leanh::lean_closure_set(v___f_4702_, 1, v_key_4695_);
        v___x_4703_ =
            crate::leanh::lean_apply_2(v_toPure_4691_, crate::leanh::lean_box(0), v___f_4702_);
        v___x_4704_ = crate::leanh::lean_apply_4(
            v_toSeq_4692_,
            crate::leanh::lean_box(0),
            crate::leanh::lean_box(0),
            v___x_4703_,
            v___f_4700_,
        );
        v___x_4705_ = crate::leanh::lean_apply_4(
            v_toSeq_4692_,
            crate::leanh::lean_box(0),
            crate::leanh::lean_box(0),
            v___x_4704_,
            v___f_4699_,
        );
        v___x_4706_ = crate::leanh::lean_apply_4(
            v_toSeq_4692_,
            crate::leanh::lean_box(0),
            crate::leanh::lean_box(0),
            v___x_4705_,
            v___f_4698_,
        );
        return v___x_4706_;
    }
}
pub unsafe fn l_Lean_RBNode_mapM___redArg___lam__0(
    mut v_inst_4707_: *mut crate::leanh::LeanObject,
    mut v_f_4708_: *mut crate::leanh::LeanObject,
    mut v_rchild_4709_: *mut crate::leanh::LeanObject,
    mut v_x_4710_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4711_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4711_ = l_Lean_RBNode_mapM___redArg(v_inst_4707_, v_f_4708_, v_rchild_4709_);
    return v___x_4711_;
}
pub unsafe fn l_Lean_RBNode_mapM(
    mut v_00_u03b1_4712_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_4713_: *mut crate::leanh::LeanObject,
    mut v_00_u03b3_4714_: *mut crate::leanh::LeanObject,
    mut v_M_4715_: *mut crate::leanh::LeanObject,
    mut v_inst_4716_: *mut crate::leanh::LeanObject,
    mut v_f_4717_: *mut crate::leanh::LeanObject,
    mut v_x_4718_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4719_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4719_ = l_Lean_RBNode_mapM___redArg(v_inst_4716_, v_f_4717_, v_x_4718_);
    return v___x_4719_;
}
pub unsafe fn l_Lean_RBNode_map___redArg(
    mut v_f_4720_: *mut crate::leanh::LeanObject,
    mut v_x_4721_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4722_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_color_4723_: u8 = 0;
    let mut v_lchild_4724_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_key_4725_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_4726_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_rchild_4727_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4729_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4730_: u8 = 0;
    let mut v___x_4731_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4732_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4733_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4735_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4736_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4737_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_4721_) == 0 {
                    crate::leanh::lean_dec(v_f_4720_);
                    v___x_4722_ = crate::leanh::lean_box(0);
                    return v___x_4722_;
                } else {
                    v_color_4723_ = crate::leanh::lean_ctor_get_uint8(
                        v_x_4721_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 4) as u32,
                    );
                    v_lchild_4724_ = crate::leanh::lean_ctor_get(v_x_4721_, 0);
                    v_key_4725_ = crate::leanh::lean_ctor_get(v_x_4721_, 1);
                    v_val_4726_ = crate::leanh::lean_ctor_get(v_x_4721_, 2);
                    v_rchild_4727_ = crate::leanh::lean_ctor_get(v_x_4721_, 3);
                    v_isSharedCheck_4737_ = (!crate::leanh::lean_is_exclusive(v_x_4721_)) as u8;
                    if v_isSharedCheck_4737_ == 0 {
                        v___x_4729_ = v_x_4721_;
                        v_isShared_4730_ = v_isSharedCheck_4737_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_rchild_4727_);
                        crate::leanh::lean_inc(v_val_4726_);
                        crate::leanh::lean_inc(v_key_4725_);
                        crate::leanh::lean_inc(v_lchild_4724_);
                        crate::leanh::lean_dec(v_x_4721_);
                        v___x_4729_ = crate::leanh::lean_box(0);
                        v_isShared_4730_ = v_isSharedCheck_4737_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                crate::leanh::lean_inc_n(v_f_4720_, 2);
                v___x_4731_ = l_Lean_RBNode_map___redArg(v_f_4720_, v_lchild_4724_);
                crate::leanh::lean_inc(v_key_4725_);
                v___x_4732_ = crate::leanh::lean_apply_2(v_f_4720_, v_key_4725_, v_val_4726_);
                v___x_4733_ = l_Lean_RBNode_map___redArg(v_f_4720_, v_rchild_4727_);
                if v_isShared_4730_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4729_, 3, v___x_4733_);
                    crate::leanh::lean_ctor_set(v___x_4729_, 2, v___x_4732_);
                    crate::leanh::lean_ctor_set(v___x_4729_, 0, v___x_4731_);
                    v___x_4735_ = v___x_4729_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4736_ = crate::leanh::lean_alloc_ctor(1, 4, (1) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4736_, 0, v___x_4731_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4736_, 1, v_key_4725_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4736_, 2, v___x_4732_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4736_, 3, v___x_4733_);
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_4736_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 4) as u32,
                        v_color_4723_,
                    );
                    v___x_4735_ = v_reuseFailAlloc_4736_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_4735_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_RBNode_map(
    mut v_00_u03b1_4738_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_4739_: *mut crate::leanh::LeanObject,
    mut v_00_u03b3_4740_: *mut crate::leanh::LeanObject,
    mut v_f_4741_: *mut crate::leanh::LeanObject,
    mut v_x_4742_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4743_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4743_ = l_Lean_RBNode_map___redArg(v_f_4741_, v_x_4742_);
    return v___x_4743_;
}
pub unsafe fn l_Lean_RBNode_fold___at___00Lean_RBNode_toArray_spec__0___redArg(
    mut v_x_4744_: *mut crate::leanh::LeanObject,
    mut v_x_4745_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_lchild_4746_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_key_4747_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_4748_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_rchild_4749_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4750_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4751_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4752_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_4745_) == 0 {
                    return v_x_4744_;
                } else {
                    v_lchild_4746_ = crate::leanh::lean_ctor_get(v_x_4745_, 0);
                    v_key_4747_ = crate::leanh::lean_ctor_get(v_x_4745_, 1);
                    v_val_4748_ = crate::leanh::lean_ctor_get(v_x_4745_, 2);
                    v_rchild_4749_ = crate::leanh::lean_ctor_get(v_x_4745_, 3);
                    v___x_4750_ = l_Lean_RBNode_fold___at___00Lean_RBNode_toArray_spec__0___redArg(
                        v_x_4744_,
                        v_lchild_4746_,
                    );
                    crate::leanh::lean_inc(v_val_4748_);
                    crate::leanh::lean_inc(v_key_4747_);
                    v___x_4751_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_4751_, 0, v_key_4747_);
                    crate::leanh::lean_ctor_set(v___x_4751_, 1, v_val_4748_);
                    v___x_4752_ = lean_array_push(v___x_4750_, v___x_4751_);
                    v_x_4744_ = v___x_4752_;
                    v_x_4745_ = v_rchild_4749_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_RBNode_fold___at___00Lean_RBNode_toArray_spec__0___redArg___boxed(
    mut v_x_4754_: *mut crate::leanh::LeanObject,
    mut v_x_4755_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4756_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4756_ =
        l_Lean_RBNode_fold___at___00Lean_RBNode_toArray_spec__0___redArg(v_x_4754_, v_x_4755_);
    crate::leanh::lean_dec(v_x_4755_);
    return v_res_4756_;
}
pub unsafe fn l_Lean_RBNode_toArray___redArg(
    mut v_n_4759_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4760_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4761_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4760_ = l_Lean_RBNode_toArray___redArg___closed__0;
    v___x_4761_ =
        l_Lean_RBNode_fold___at___00Lean_RBNode_toArray_spec__0___redArg(v___x_4760_, v_n_4759_);
    return v___x_4761_;
}
pub unsafe fn l_Lean_RBNode_toArray___redArg___boxed(
    mut v_n_4762_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4763_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4763_ = l_Lean_RBNode_toArray___redArg(v_n_4762_);
    crate::leanh::lean_dec(v_n_4762_);
    return v_res_4763_;
}
pub unsafe fn l_Lean_RBNode_toArray(
    mut v_00_u03b1_4764_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_4765_: *mut crate::leanh::LeanObject,
    mut v_n_4766_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4767_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4767_ = l_Lean_RBNode_toArray___redArg(v_n_4766_);
    return v___x_4767_;
}
pub unsafe fn l_Lean_RBNode_toArray___boxed(
    mut v_00_u03b1_4768_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_4769_: *mut crate::leanh::LeanObject,
    mut v_n_4770_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4771_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4771_ = l_Lean_RBNode_toArray(v_00_u03b1_4768_, v_00_u03b2_4769_, v_n_4770_);
    crate::leanh::lean_dec(v_n_4770_);
    return v_res_4771_;
}
pub unsafe fn l_Lean_RBNode_fold___at___00Lean_RBNode_toArray_spec__0(
    mut v_00_u03b1_4772_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_4773_: *mut crate::leanh::LeanObject,
    mut v_x_4774_: *mut crate::leanh::LeanObject,
    mut v_x_4775_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4776_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4776_ =
        l_Lean_RBNode_fold___at___00Lean_RBNode_toArray_spec__0___redArg(v_x_4774_, v_x_4775_);
    return v___x_4776_;
}
pub unsafe fn l_Lean_RBNode_fold___at___00Lean_RBNode_toArray_spec__0___boxed(
    mut v_00_u03b1_4777_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_4778_: *mut crate::leanh::LeanObject,
    mut v_x_4779_: *mut crate::leanh::LeanObject,
    mut v_x_4780_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4781_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4781_ = l_Lean_RBNode_fold___at___00Lean_RBNode_toArray_spec__0(
        v_00_u03b1_4777_,
        v_00_u03b2_4778_,
        v_x_4779_,
        v_x_4780_,
    );
    crate::leanh::lean_dec(v_x_4780_);
    return v_res_4781_;
}
pub unsafe fn l_Lean_RBNode_instEmptyCollection(
    mut v_00_u03b1_4782_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_4783_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4784_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4784_ = crate::leanh::lean_box(0);
    return v___x_4784_;
}
pub unsafe fn l_Lean_mkRBMap(
    mut v_00_u03b1_4785_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_4786_: *mut crate::leanh::LeanObject,
    mut v_cmp_4787_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4788_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4788_ = crate::leanh::lean_box(0);
    return v___x_4788_;
}
pub unsafe fn l_Lean_mkRBMap___boxed(
    mut v_00_u03b1_4789_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_4790_: *mut crate::leanh::LeanObject,
    mut v_cmp_4791_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4792_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4792_ = l_Lean_mkRBMap(v_00_u03b1_4789_, v_00_u03b2_4790_, v_cmp_4791_);
    crate::leanh::lean_dec_ref(v_cmp_4791_);
    return v_res_4792_;
}
pub unsafe fn l_Lean_RBMap_empty(
    mut v___y_4793_: *mut crate::leanh::LeanObject,
    mut v___y_4794_: *mut crate::leanh::LeanObject,
    mut v___y_4795_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4796_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4796_ = crate::leanh::lean_box(0);
    return v___x_4796_;
}
pub unsafe fn l_Lean_RBMap_empty___boxed(
    mut v___y_4797_: *mut crate::leanh::LeanObject,
    mut v___y_4798_: *mut crate::leanh::LeanObject,
    mut v___y_4799_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4800_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4800_ = l_Lean_RBMap_empty(v___y_4797_, v___y_4798_, v___y_4799_);
    crate::leanh::lean_dec_ref(v___y_4799_);
    return v_res_4800_;
}
pub unsafe fn l_Lean_instEmptyCollectionRBMap(
    mut v_00_u03b1_4801_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_4802_: *mut crate::leanh::LeanObject,
    mut v_cmp_4803_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4804_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4804_ = crate::leanh::lean_box(0);
    return v___x_4804_;
}
pub unsafe fn l_Lean_instEmptyCollectionRBMap___boxed(
    mut v_00_u03b1_4805_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_4806_: *mut crate::leanh::LeanObject,
    mut v_cmp_4807_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4808_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4808_ = l_Lean_instEmptyCollectionRBMap(v_00_u03b1_4805_, v_00_u03b2_4806_, v_cmp_4807_);
    crate::leanh::lean_dec_ref(v_cmp_4807_);
    return v_res_4808_;
}
pub unsafe fn l_Lean_instInhabitedRBMap(
    mut v_00_u03b1_4809_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_4810_: *mut crate::leanh::LeanObject,
    mut v_cmp_4811_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4812_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4812_ = crate::leanh::lean_box(0);
    return v___x_4812_;
}
pub unsafe fn l_Lean_instInhabitedRBMap___boxed(
    mut v_00_u03b1_4813_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_4814_: *mut crate::leanh::LeanObject,
    mut v_cmp_4815_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4816_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4816_ = l_Lean_instInhabitedRBMap(v_00_u03b1_4813_, v_00_u03b2_4814_, v_cmp_4815_);
    crate::leanh::lean_dec_ref(v_cmp_4815_);
    return v_res_4816_;
}
pub unsafe fn l_Lean_RBMap_depth___redArg(
    mut v_f_4817_: *mut crate::leanh::LeanObject,
    mut v_t_4818_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4819_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4819_ = l_Lean_RBNode_depth___redArg(v_f_4817_, v_t_4818_);
    return v___x_4819_;
}
pub unsafe fn l_Lean_RBMap_depth___redArg___boxed(
    mut v_f_4820_: *mut crate::leanh::LeanObject,
    mut v_t_4821_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4822_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4822_ = l_Lean_RBMap_depth___redArg(v_f_4820_, v_t_4821_);
    crate::leanh::lean_dec(v_t_4821_);
    return v_res_4822_;
}
pub unsafe fn l_Lean_RBMap_depth(
    mut v_00_u03b1_4823_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_4824_: *mut crate::leanh::LeanObject,
    mut v_cmp_4825_: *mut crate::leanh::LeanObject,
    mut v_f_4826_: *mut crate::leanh::LeanObject,
    mut v_t_4827_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4828_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4828_ = l_Lean_RBNode_depth___redArg(v_f_4826_, v_t_4827_);
    return v___x_4828_;
}
pub unsafe fn l_Lean_RBMap_depth___boxed(
    mut v_00_u03b1_4829_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_4830_: *mut crate::leanh::LeanObject,
    mut v_cmp_4831_: *mut crate::leanh::LeanObject,
    mut v_f_4832_: *mut crate::leanh::LeanObject,
    mut v_t_4833_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4834_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4834_ = l_Lean_RBMap_depth(
        v_00_u03b1_4829_,
        v_00_u03b2_4830_,
        v_cmp_4831_,
        v_f_4832_,
        v_t_4833_,
    );
    crate::leanh::lean_dec(v_t_4833_);
    crate::leanh::lean_dec_ref(v_cmp_4831_);
    return v_res_4834_;
}
pub unsafe fn l_Lean_RBMap_isSingleton___redArg(
    mut v_t_4835_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_4836_: u8 = 0;
    v___x_4836_ = l_Lean_RBNode_isSingleton___redArg(v_t_4835_);
    return v___x_4836_;
}
pub unsafe fn l_Lean_RBMap_isSingleton___redArg___boxed(
    mut v_t_4837_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4838_: u8 = 0;
    let mut v_r_4839_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4838_ = l_Lean_RBMap_isSingleton___redArg(v_t_4837_);
    crate::leanh::lean_dec(v_t_4837_);
    v_r_4839_ = crate::leanh::lean_box((v_res_4838_) as usize);
    return v_r_4839_;
}
pub unsafe fn l_Lean_RBMap_isSingleton(
    mut v_00_u03b1_4840_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_4841_: *mut crate::leanh::LeanObject,
    mut v_cmp_4842_: *mut crate::leanh::LeanObject,
    mut v_t_4843_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_4844_: u8 = 0;
    v___x_4844_ = l_Lean_RBNode_isSingleton___redArg(v_t_4843_);
    return v___x_4844_;
}
pub unsafe fn l_Lean_RBMap_isSingleton___boxed(
    mut v_00_u03b1_4845_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_4846_: *mut crate::leanh::LeanObject,
    mut v_cmp_4847_: *mut crate::leanh::LeanObject,
    mut v_t_4848_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4849_: u8 = 0;
    let mut v_r_4850_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4849_ =
        l_Lean_RBMap_isSingleton(v_00_u03b1_4845_, v_00_u03b2_4846_, v_cmp_4847_, v_t_4848_);
    crate::leanh::lean_dec(v_t_4848_);
    crate::leanh::lean_dec_ref(v_cmp_4847_);
    v_r_4850_ = crate::leanh::lean_box((v_res_4849_) as usize);
    return v_r_4850_;
}
pub unsafe fn l_Lean_RBMap_fold___redArg(
    mut v_f_4851_: *mut crate::leanh::LeanObject,
    mut v_x_4852_: *mut crate::leanh::LeanObject,
    mut v_x_4853_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4854_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4854_ = l_Lean_RBNode_fold___redArg(v_f_4851_, v_x_4852_, v_x_4853_);
    return v___x_4854_;
}
pub unsafe fn l_Lean_RBMap_fold(
    mut v_00_u03b1_4855_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_4856_: *mut crate::leanh::LeanObject,
    mut v_00_u03c3_4857_: *mut crate::leanh::LeanObject,
    mut v_cmp_4858_: *mut crate::leanh::LeanObject,
    mut v_f_4859_: *mut crate::leanh::LeanObject,
    mut v_x_4860_: *mut crate::leanh::LeanObject,
    mut v_x_4861_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4862_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4862_ = l_Lean_RBNode_fold___redArg(v_f_4859_, v_x_4860_, v_x_4861_);
    return v___x_4862_;
}
pub unsafe fn l_Lean_RBMap_fold___boxed(
    mut v_00_u03b1_4863_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_4864_: *mut crate::leanh::LeanObject,
    mut v_00_u03c3_4865_: *mut crate::leanh::LeanObject,
    mut v_cmp_4866_: *mut crate::leanh::LeanObject,
    mut v_f_4867_: *mut crate::leanh::LeanObject,
    mut v_x_4868_: *mut crate::leanh::LeanObject,
    mut v_x_4869_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4870_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4870_ = l_Lean_RBMap_fold(
        v_00_u03b1_4863_,
        v_00_u03b2_4864_,
        v_00_u03c3_4865_,
        v_cmp_4866_,
        v_f_4867_,
        v_x_4868_,
        v_x_4869_,
    );
    crate::leanh::lean_dec_ref(v_cmp_4866_);
    return v_res_4870_;
}
pub unsafe fn l_Lean_RBMap_revFold___redArg(
    mut v_f_4871_: *mut crate::leanh::LeanObject,
    mut v_x_4872_: *mut crate::leanh::LeanObject,
    mut v_x_4873_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4874_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4874_ = l_Lean_RBNode_revFold___redArg(v_f_4871_, v_x_4872_, v_x_4873_);
    return v___x_4874_;
}
pub unsafe fn l_Lean_RBMap_revFold(
    mut v_00_u03b1_4875_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_4876_: *mut crate::leanh::LeanObject,
    mut v_00_u03c3_4877_: *mut crate::leanh::LeanObject,
    mut v_cmp_4878_: *mut crate::leanh::LeanObject,
    mut v_f_4879_: *mut crate::leanh::LeanObject,
    mut v_x_4880_: *mut crate::leanh::LeanObject,
    mut v_x_4881_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4882_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4882_ = l_Lean_RBNode_revFold___redArg(v_f_4879_, v_x_4880_, v_x_4881_);
    return v___x_4882_;
}
pub unsafe fn l_Lean_RBMap_revFold___boxed(
    mut v_00_u03b1_4883_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_4884_: *mut crate::leanh::LeanObject,
    mut v_00_u03c3_4885_: *mut crate::leanh::LeanObject,
    mut v_cmp_4886_: *mut crate::leanh::LeanObject,
    mut v_f_4887_: *mut crate::leanh::LeanObject,
    mut v_x_4888_: *mut crate::leanh::LeanObject,
    mut v_x_4889_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4890_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4890_ = l_Lean_RBMap_revFold(
        v_00_u03b1_4883_,
        v_00_u03b2_4884_,
        v_00_u03c3_4885_,
        v_cmp_4886_,
        v_f_4887_,
        v_x_4888_,
        v_x_4889_,
    );
    crate::leanh::lean_dec_ref(v_cmp_4886_);
    return v_res_4890_;
}
pub unsafe fn l_Lean_RBMap_foldM___redArg(
    mut v_inst_4891_: *mut crate::leanh::LeanObject,
    mut v_f_4892_: *mut crate::leanh::LeanObject,
    mut v_x_4893_: *mut crate::leanh::LeanObject,
    mut v_x_4894_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4895_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4895_ = l_Lean_RBNode_foldM___redArg(v_inst_4891_, v_f_4892_, v_x_4893_, v_x_4894_);
    return v___x_4895_;
}
pub unsafe fn l_Lean_RBMap_foldM(
    mut v_00_u03b1_4896_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_4897_: *mut crate::leanh::LeanObject,
    mut v_00_u03c3_4898_: *mut crate::leanh::LeanObject,
    mut v_cmp_4899_: *mut crate::leanh::LeanObject,
    mut v_m_4900_: *mut crate::leanh::LeanObject,
    mut v_inst_4901_: *mut crate::leanh::LeanObject,
    mut v_f_4902_: *mut crate::leanh::LeanObject,
    mut v_x_4903_: *mut crate::leanh::LeanObject,
    mut v_x_4904_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4905_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4905_ = l_Lean_RBNode_foldM___redArg(v_inst_4901_, v_f_4902_, v_x_4903_, v_x_4904_);
    return v___x_4905_;
}
pub unsafe fn l_Lean_RBMap_foldM___boxed(
    mut v_00_u03b1_4906_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_4907_: *mut crate::leanh::LeanObject,
    mut v_00_u03c3_4908_: *mut crate::leanh::LeanObject,
    mut v_cmp_4909_: *mut crate::leanh::LeanObject,
    mut v_m_4910_: *mut crate::leanh::LeanObject,
    mut v_inst_4911_: *mut crate::leanh::LeanObject,
    mut v_f_4912_: *mut crate::leanh::LeanObject,
    mut v_x_4913_: *mut crate::leanh::LeanObject,
    mut v_x_4914_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4915_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4915_ = l_Lean_RBMap_foldM(
        v_00_u03b1_4906_,
        v_00_u03b2_4907_,
        v_00_u03c3_4908_,
        v_cmp_4909_,
        v_m_4910_,
        v_inst_4911_,
        v_f_4912_,
        v_x_4913_,
        v_x_4914_,
    );
    crate::leanh::lean_dec_ref(v_cmp_4909_);
    return v_res_4915_;
}
pub unsafe fn l_Lean_RBMap_forM___redArg___lam__0(
    mut v_f_4916_: *mut crate::leanh::LeanObject,
    mut v_x_4917_: *mut crate::leanh::LeanObject,
    mut v_k_4918_: *mut crate::leanh::LeanObject,
    mut v_v_4919_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4920_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4920_ = crate::leanh::lean_apply_2(v_f_4916_, v_k_4918_, v_v_4919_);
    return v___x_4920_;
}
pub unsafe fn l_Lean_RBMap_forM___redArg(
    mut v_inst_4921_: *mut crate::leanh::LeanObject,
    mut v_f_4922_: *mut crate::leanh::LeanObject,
    mut v_t_4923_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_4924_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4925_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4926_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_4924_ = crate::leanh::lean_alloc_closure(
        l_Lean_RBMap_forM___redArg___lam__0 as *mut core::ffi::c_void,
        4,
        1,
    );
    crate::leanh::lean_closure_set(v___f_4924_, 0, v_f_4922_);
    v___x_4925_ = crate::leanh::lean_box(0);
    v___x_4926_ = l_Lean_RBNode_foldM___redArg(v_inst_4921_, v___f_4924_, v___x_4925_, v_t_4923_);
    return v___x_4926_;
}
pub unsafe fn l_Lean_RBMap_forM(
    mut v_00_u03b1_4927_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_4928_: *mut crate::leanh::LeanObject,
    mut v_cmp_4929_: *mut crate::leanh::LeanObject,
    mut v_m_4930_: *mut crate::leanh::LeanObject,
    mut v_inst_4931_: *mut crate::leanh::LeanObject,
    mut v_f_4932_: *mut crate::leanh::LeanObject,
    mut v_t_4933_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_4934_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4935_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4936_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_4934_ = crate::leanh::lean_alloc_closure(
        l_Lean_RBMap_forM___redArg___lam__0 as *mut core::ffi::c_void,
        4,
        1,
    );
    crate::leanh::lean_closure_set(v___f_4934_, 0, v_f_4932_);
    v___x_4935_ = crate::leanh::lean_box(0);
    v___x_4936_ = l_Lean_RBNode_foldM___redArg(v_inst_4931_, v___f_4934_, v___x_4935_, v_t_4933_);
    return v___x_4936_;
}
pub unsafe fn l_Lean_RBMap_forM___boxed(
    mut v_00_u03b1_4937_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_4938_: *mut crate::leanh::LeanObject,
    mut v_cmp_4939_: *mut crate::leanh::LeanObject,
    mut v_m_4940_: *mut crate::leanh::LeanObject,
    mut v_inst_4941_: *mut crate::leanh::LeanObject,
    mut v_f_4942_: *mut crate::leanh::LeanObject,
    mut v_t_4943_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4944_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4944_ = l_Lean_RBMap_forM(
        v_00_u03b1_4937_,
        v_00_u03b2_4938_,
        v_cmp_4939_,
        v_m_4940_,
        v_inst_4941_,
        v_f_4942_,
        v_t_4943_,
    );
    crate::leanh::lean_dec_ref(v_cmp_4939_);
    return v_res_4944_;
}
pub unsafe fn l_Lean_RBMap_forIn___redArg___lam__0(
    mut v_f_4945_: *mut crate::leanh::LeanObject,
    mut v_a_4946_: *mut crate::leanh::LeanObject,
    mut v_b_4947_: *mut crate::leanh::LeanObject,
    mut v_acc_4948_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4949_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4950_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4949_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_4949_, 0, v_a_4946_);
    crate::leanh::lean_ctor_set(v___x_4949_, 1, v_b_4947_);
    v___x_4950_ = crate::leanh::lean_apply_2(v_f_4945_, v___x_4949_, v_acc_4948_);
    return v___x_4950_;
}
pub unsafe fn l_Lean_RBMap_forIn___redArg(
    mut v_inst_4951_: *mut crate::leanh::LeanObject,
    mut v_t_4952_: *mut crate::leanh::LeanObject,
    mut v_init_4953_: *mut crate::leanh::LeanObject,
    mut v_f_4954_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toApplicative_4955_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_4956_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_4957_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4958_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4959_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4960_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4961_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_4955_ = crate::leanh::lean_ctor_get(v_inst_4951_, 0);
    v_toBind_4956_ = crate::leanh::lean_ctor_get(v_inst_4951_, 1);
    crate::leanh::lean_inc(v_toBind_4956_);
    v_toPure_4957_ = crate::leanh::lean_ctor_get(v_toApplicative_4955_, 1);
    crate::leanh::lean_inc(v_toPure_4957_);
    v___f_4958_ = crate::leanh::lean_alloc_closure(
        l_Lean_RBMap_forIn___redArg___lam__0 as *mut core::ffi::c_void,
        4,
        1,
    );
    crate::leanh::lean_closure_set(v___f_4958_, 0, v_f_4954_);
    v___x_4959_ = l___private_Lean_Data_RBMap_0__Lean_RBNode_forIn_visit___redArg(
        v_inst_4951_,
        v___f_4958_,
        v_t_4952_,
        v_init_4953_,
    );
    v___f_4960_ = crate::leanh::lean_alloc_closure(
        l_Lean_RBNode_forIn___redArg___lam__0 as *mut core::ffi::c_void,
        2,
        1,
    );
    crate::leanh::lean_closure_set(v___f_4960_, 0, v_toPure_4957_);
    v___x_4961_ = crate::leanh::lean_apply_4(
        v_toBind_4956_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___x_4959_,
        v___f_4960_,
    );
    return v___x_4961_;
}
pub unsafe fn l_Lean_RBMap_forIn(
    mut v_00_u03b1_4962_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_4963_: *mut crate::leanh::LeanObject,
    mut v_00_u03c3_4964_: *mut crate::leanh::LeanObject,
    mut v_cmp_4965_: *mut crate::leanh::LeanObject,
    mut v_m_4966_: *mut crate::leanh::LeanObject,
    mut v_inst_4967_: *mut crate::leanh::LeanObject,
    mut v_t_4968_: *mut crate::leanh::LeanObject,
    mut v_init_4969_: *mut crate::leanh::LeanObject,
    mut v_f_4970_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toApplicative_4971_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_4972_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_4973_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4974_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4975_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4976_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4977_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_4971_ = crate::leanh::lean_ctor_get(v_inst_4967_, 0);
    v_toBind_4972_ = crate::leanh::lean_ctor_get(v_inst_4967_, 1);
    crate::leanh::lean_inc(v_toBind_4972_);
    v_toPure_4973_ = crate::leanh::lean_ctor_get(v_toApplicative_4971_, 1);
    crate::leanh::lean_inc(v_toPure_4973_);
    v___f_4974_ = crate::leanh::lean_alloc_closure(
        l_Lean_RBMap_forIn___redArg___lam__0 as *mut core::ffi::c_void,
        4,
        1,
    );
    crate::leanh::lean_closure_set(v___f_4974_, 0, v_f_4970_);
    v___x_4975_ = l___private_Lean_Data_RBMap_0__Lean_RBNode_forIn_visit___redArg(
        v_inst_4967_,
        v___f_4974_,
        v_t_4968_,
        v_init_4969_,
    );
    v___f_4976_ = crate::leanh::lean_alloc_closure(
        l_Lean_RBNode_forIn___redArg___lam__0 as *mut core::ffi::c_void,
        2,
        1,
    );
    crate::leanh::lean_closure_set(v___f_4976_, 0, v_toPure_4973_);
    v___x_4977_ = crate::leanh::lean_apply_4(
        v_toBind_4972_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___x_4975_,
        v___f_4976_,
    );
    return v___x_4977_;
}
pub unsafe fn l_Lean_RBMap_forIn___boxed(
    mut v_00_u03b1_4978_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_4979_: *mut crate::leanh::LeanObject,
    mut v_00_u03c3_4980_: *mut crate::leanh::LeanObject,
    mut v_cmp_4981_: *mut crate::leanh::LeanObject,
    mut v_m_4982_: *mut crate::leanh::LeanObject,
    mut v_inst_4983_: *mut crate::leanh::LeanObject,
    mut v_t_4984_: *mut crate::leanh::LeanObject,
    mut v_init_4985_: *mut crate::leanh::LeanObject,
    mut v_f_4986_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4987_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4987_ = l_Lean_RBMap_forIn(
        v_00_u03b1_4978_,
        v_00_u03b2_4979_,
        v_00_u03c3_4980_,
        v_cmp_4981_,
        v_m_4982_,
        v_inst_4983_,
        v_t_4984_,
        v_init_4985_,
        v_f_4986_,
    );
    crate::leanh::lean_dec_ref(v_cmp_4981_);
    return v_res_4987_;
}
pub unsafe fn l_Lean_RBMap_instForInProdOfMonad___redArg___lam__0(
    mut v___y_4988_: *mut crate::leanh::LeanObject,
    mut v_a_4989_: *mut crate::leanh::LeanObject,
    mut v_b_4990_: *mut crate::leanh::LeanObject,
    mut v_acc_4991_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4992_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4993_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4992_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_4992_, 0, v_a_4989_);
    crate::leanh::lean_ctor_set(v___x_4992_, 1, v_b_4990_);
    v___x_4993_ = crate::leanh::lean_apply_2(v___y_4988_, v___x_4992_, v_acc_4991_);
    return v___x_4993_;
}
pub unsafe fn l_Lean_RBMap_instForInProdOfMonad___redArg___lam__2(
    mut v_inst_4994_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_4995_: *mut crate::leanh::LeanObject,
    mut v___y_4996_: *mut crate::leanh::LeanObject,
    mut v___y_4997_: *mut crate::leanh::LeanObject,
    mut v___y_4998_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toApplicative_4999_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_5000_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_5001_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_5002_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5003_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_5004_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5005_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_4999_ = crate::leanh::lean_ctor_get(v_inst_4994_, 0);
    v_toBind_5000_ = crate::leanh::lean_ctor_get(v_inst_4994_, 1);
    crate::leanh::lean_inc(v_toBind_5000_);
    v_toPure_5001_ = crate::leanh::lean_ctor_get(v_toApplicative_4999_, 1);
    crate::leanh::lean_inc(v_toPure_5001_);
    v___f_5002_ = crate::leanh::lean_alloc_closure(
        l_Lean_RBMap_instForInProdOfMonad___redArg___lam__0 as *mut core::ffi::c_void,
        4,
        1,
    );
    crate::leanh::lean_closure_set(v___f_5002_, 0, v___y_4998_);
    v___x_5003_ = l___private_Lean_Data_RBMap_0__Lean_RBNode_forIn_visit___redArg(
        v_inst_4994_,
        v___f_5002_,
        v___y_4996_,
        v___y_4997_,
    );
    v___f_5004_ = crate::leanh::lean_alloc_closure(
        l_Lean_RBNode_forIn___redArg___lam__0 as *mut core::ffi::c_void,
        2,
        1,
    );
    crate::leanh::lean_closure_set(v___f_5004_, 0, v_toPure_5001_);
    v___x_5005_ = crate::leanh::lean_apply_4(
        v_toBind_5000_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___x_5003_,
        v___f_5004_,
    );
    return v___x_5005_;
}
pub unsafe fn l_Lean_RBMap_instForInProdOfMonad___redArg(
    mut v_inst_5006_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_5007_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_5007_ = crate::leanh::lean_alloc_closure(
        l_Lean_RBMap_instForInProdOfMonad___redArg___lam__2 as *mut core::ffi::c_void,
        5,
        1,
    );
    crate::leanh::lean_closure_set(v___f_5007_, 0, v_inst_5006_);
    return v___f_5007_;
}
pub unsafe fn l_Lean_RBMap_instForInProdOfMonad(
    mut v_00_u03b1_5008_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_5009_: *mut crate::leanh::LeanObject,
    mut v_cmp_5010_: *mut crate::leanh::LeanObject,
    mut v_m_5011_: *mut crate::leanh::LeanObject,
    mut v_inst_5012_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_5013_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_5013_ = crate::leanh::lean_alloc_closure(
        l_Lean_RBMap_instForInProdOfMonad___redArg___lam__2 as *mut core::ffi::c_void,
        5,
        1,
    );
    crate::leanh::lean_closure_set(v___f_5013_, 0, v_inst_5012_);
    return v___f_5013_;
}
pub unsafe fn l_Lean_RBMap_instForInProdOfMonad___boxed(
    mut v_00_u03b1_5014_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_5015_: *mut crate::leanh::LeanObject,
    mut v_cmp_5016_: *mut crate::leanh::LeanObject,
    mut v_m_5017_: *mut crate::leanh::LeanObject,
    mut v_inst_5018_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5019_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5019_ = l_Lean_RBMap_instForInProdOfMonad(
        v_00_u03b1_5014_,
        v_00_u03b2_5015_,
        v_cmp_5016_,
        v_m_5017_,
        v_inst_5018_,
    );
    crate::leanh::lean_dec_ref(v_cmp_5016_);
    return v_res_5019_;
}
pub unsafe fn l_Lean_RBMap_isEmpty___redArg(mut v_x_5020_: *mut crate::leanh::LeanObject) -> u8 {
    if crate::leanh::lean_obj_tag(v_x_5020_) == 0 {
        let mut v___x_5021_: u8 = 0;
        v___x_5021_ = 1;
        return v___x_5021_;
    } else {
        let mut v___x_5022_: u8 = 0;
        v___x_5022_ = 0;
        return v___x_5022_;
    }
}
pub unsafe fn l_Lean_RBMap_isEmpty___redArg___boxed(
    mut v_x_5023_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5024_: u8 = 0;
    let mut v_r_5025_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5024_ = l_Lean_RBMap_isEmpty___redArg(v_x_5023_);
    crate::leanh::lean_dec(v_x_5023_);
    v_r_5025_ = crate::leanh::lean_box((v_res_5024_) as usize);
    return v_r_5025_;
}
pub unsafe fn l_Lean_RBMap_isEmpty(
    mut v_00_u03b1_5026_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_5027_: *mut crate::leanh::LeanObject,
    mut v_cmp_5028_: *mut crate::leanh::LeanObject,
    mut v_x_5029_: *mut crate::leanh::LeanObject,
) -> u8 {
    if crate::leanh::lean_obj_tag(v_x_5029_) == 0 {
        let mut v___x_5030_: u8 = 0;
        v___x_5030_ = 1;
        return v___x_5030_;
    } else {
        let mut v___x_5031_: u8 = 0;
        v___x_5031_ = 0;
        return v___x_5031_;
    }
}
pub unsafe fn l_Lean_RBMap_isEmpty___boxed(
    mut v_00_u03b1_5032_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_5033_: *mut crate::leanh::LeanObject,
    mut v_cmp_5034_: *mut crate::leanh::LeanObject,
    mut v_x_5035_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5036_: u8 = 0;
    let mut v_r_5037_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5036_ = l_Lean_RBMap_isEmpty(v_00_u03b1_5032_, v_00_u03b2_5033_, v_cmp_5034_, v_x_5035_);
    crate::leanh::lean_dec(v_x_5035_);
    crate::leanh::lean_dec_ref(v_cmp_5034_);
    v_r_5037_ = crate::leanh::lean_box((v_res_5036_) as usize);
    return v_r_5037_;
}
pub unsafe fn l_Lean_RBMap_toList___redArg___lam__0(
    mut v_ps_5038_: *mut crate::leanh::LeanObject,
    mut v_k_5039_: *mut crate::leanh::LeanObject,
    mut v_v_5040_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5041_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5042_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5041_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_5041_, 0, v_k_5039_);
    crate::leanh::lean_ctor_set(v___x_5041_, 1, v_v_5040_);
    v___x_5042_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_5042_, 0, v___x_5041_);
    crate::leanh::lean_ctor_set(v___x_5042_, 1, v_ps_5038_);
    return v___x_5042_;
}
pub unsafe fn l_Lean_RBMap_toList___redArg(
    mut v_x_5044_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_5045_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5046_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5047_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_5045_ = l_Lean_RBMap_toList___redArg___closed__0;
    v___x_5046_ = crate::leanh::lean_box(0);
    v___x_5047_ = l_Lean_RBNode_revFold___redArg(v___f_5045_, v___x_5046_, v_x_5044_);
    return v___x_5047_;
}
pub unsafe fn l_Lean_RBMap_toList(
    mut v_00_u03b1_5048_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_5049_: *mut crate::leanh::LeanObject,
    mut v_cmp_5050_: *mut crate::leanh::LeanObject,
    mut v_x_5051_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5052_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5052_ = l_Lean_RBMap_toList___redArg(v_x_5051_);
    return v___x_5052_;
}
pub unsafe fn l_Lean_RBMap_toList___boxed(
    mut v_00_u03b1_5053_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_5054_: *mut crate::leanh::LeanObject,
    mut v_cmp_5055_: *mut crate::leanh::LeanObject,
    mut v_x_5056_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5057_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5057_ = l_Lean_RBMap_toList(v_00_u03b1_5053_, v_00_u03b2_5054_, v_cmp_5055_, v_x_5056_);
    crate::leanh::lean_dec_ref(v_cmp_5055_);
    return v_res_5057_;
}
pub unsafe fn l_Lean_RBMap_toArray___redArg___lam__0(
    mut v_ps_5058_: *mut crate::leanh::LeanObject,
    mut v_k_5059_: *mut crate::leanh::LeanObject,
    mut v_v_5060_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5061_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5062_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5061_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_5061_, 0, v_k_5059_);
    crate::leanh::lean_ctor_set(v___x_5061_, 1, v_v_5060_);
    v___x_5062_ = lean_array_push(v_ps_5058_, v___x_5061_);
    return v___x_5062_;
}
pub unsafe fn l_Lean_RBMap_toArray___redArg(
    mut v_x_5066_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_5067_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5068_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5069_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_5067_ = l_Lean_RBMap_toArray___redArg___closed__0;
    v___x_5068_ = l_Lean_RBMap_toArray___redArg___closed__1;
    v___x_5069_ = l_Lean_RBNode_fold___redArg(v___f_5067_, v___x_5068_, v_x_5066_);
    return v___x_5069_;
}
pub unsafe fn l_Lean_RBMap_toArray(
    mut v_00_u03b1_5070_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_5071_: *mut crate::leanh::LeanObject,
    mut v_cmp_5072_: *mut crate::leanh::LeanObject,
    mut v_x_5073_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5074_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5074_ = l_Lean_RBMap_toArray___redArg(v_x_5073_);
    return v___x_5074_;
}
pub unsafe fn l_Lean_RBMap_toArray___boxed(
    mut v_00_u03b1_5075_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_5076_: *mut crate::leanh::LeanObject,
    mut v_cmp_5077_: *mut crate::leanh::LeanObject,
    mut v_x_5078_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5079_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5079_ = l_Lean_RBMap_toArray(v_00_u03b1_5075_, v_00_u03b2_5076_, v_cmp_5077_, v_x_5078_);
    crate::leanh::lean_dec_ref(v_cmp_5077_);
    return v_res_5079_;
}
pub unsafe fn l_Lean_RBMap_min___redArg(
    mut v_x_5080_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5081_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5082_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_5083_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5085_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5086_: u8 = 0;
    let mut v_fst_5087_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_5088_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5090_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5091_: u8 = 0;
    let mut v___x_5093_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5095_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5096_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5097_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5098_: u8 = 0;
    let mut v_isSharedCheck_5099_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5081_ = l_Lean_RBNode_min___redArg(v_x_5080_);
                if crate::leanh::lean_obj_tag(v___x_5081_) == 0 {
                    v___x_5082_ = crate::leanh::lean_box(0);
                    return v___x_5082_;
                } else {
                    v_val_5083_ = crate::leanh::lean_ctor_get(v___x_5081_, 0);
                    v_isSharedCheck_5099_ = (!crate::leanh::lean_is_exclusive(v___x_5081_)) as u8;
                    if v_isSharedCheck_5099_ == 0 {
                        v___x_5085_ = v___x_5081_;
                        v_isShared_5086_ = v_isSharedCheck_5099_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_val_5083_);
                        crate::leanh::lean_dec(v___x_5081_);
                        v___x_5085_ = crate::leanh::lean_box(0);
                        v_isShared_5086_ = v_isSharedCheck_5099_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v_fst_5087_ = crate::leanh::lean_ctor_get(v_val_5083_, 0);
                v_snd_5088_ = crate::leanh::lean_ctor_get(v_val_5083_, 1);
                v_isSharedCheck_5098_ = (!crate::leanh::lean_is_exclusive(v_val_5083_)) as u8;
                if v_isSharedCheck_5098_ == 0 {
                    v___x_5090_ = v_val_5083_;
                    v_isShared_5091_ = v_isSharedCheck_5098_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_snd_5088_);
                    crate::leanh::lean_inc(v_fst_5087_);
                    crate::leanh::lean_dec(v_val_5083_);
                    v___x_5090_ = crate::leanh::lean_box(0);
                    v_isShared_5091_ = v_isSharedCheck_5098_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                if v_isShared_5091_ == 0 {
                    v___x_5093_ = v___x_5090_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_5097_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5097_, 0, v_fst_5087_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5097_, 1, v_snd_5088_);
                    v___x_5093_ = v_reuseFailAlloc_5097_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_5086_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_5085_, 0, v___x_5093_);
                    v___x_5095_ = v___x_5085_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_5096_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5096_, 0, v___x_5093_);
                    v___x_5095_ = v_reuseFailAlloc_5096_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_5095_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_RBMap_min___redArg___boxed(
    mut v_x_5100_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5101_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5101_ = l_Lean_RBMap_min___redArg(v_x_5100_);
    crate::leanh::lean_dec(v_x_5100_);
    return v_res_5101_;
}
pub unsafe fn l_Lean_RBMap_min(
    mut v_00_u03b1_5102_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_5103_: *mut crate::leanh::LeanObject,
    mut v_cmp_5104_: *mut crate::leanh::LeanObject,
    mut v_x_5105_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5106_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5107_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_5108_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5110_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5111_: u8 = 0;
    let mut v_fst_5112_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_5113_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5115_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5116_: u8 = 0;
    let mut v___x_5118_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5120_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5121_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5122_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5123_: u8 = 0;
    let mut v_isSharedCheck_5124_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5106_ = l_Lean_RBNode_min___redArg(v_x_5105_);
                if crate::leanh::lean_obj_tag(v___x_5106_) == 0 {
                    v___x_5107_ = crate::leanh::lean_box(0);
                    return v___x_5107_;
                } else {
                    v_val_5108_ = crate::leanh::lean_ctor_get(v___x_5106_, 0);
                    v_isSharedCheck_5124_ = (!crate::leanh::lean_is_exclusive(v___x_5106_)) as u8;
                    if v_isSharedCheck_5124_ == 0 {
                        v___x_5110_ = v___x_5106_;
                        v_isShared_5111_ = v_isSharedCheck_5124_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_val_5108_);
                        crate::leanh::lean_dec(v___x_5106_);
                        v___x_5110_ = crate::leanh::lean_box(0);
                        v_isShared_5111_ = v_isSharedCheck_5124_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v_fst_5112_ = crate::leanh::lean_ctor_get(v_val_5108_, 0);
                v_snd_5113_ = crate::leanh::lean_ctor_get(v_val_5108_, 1);
                v_isSharedCheck_5123_ = (!crate::leanh::lean_is_exclusive(v_val_5108_)) as u8;
                if v_isSharedCheck_5123_ == 0 {
                    v___x_5115_ = v_val_5108_;
                    v_isShared_5116_ = v_isSharedCheck_5123_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_snd_5113_);
                    crate::leanh::lean_inc(v_fst_5112_);
                    crate::leanh::lean_dec(v_val_5108_);
                    v___x_5115_ = crate::leanh::lean_box(0);
                    v_isShared_5116_ = v_isSharedCheck_5123_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                if v_isShared_5116_ == 0 {
                    v___x_5118_ = v___x_5115_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_5122_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5122_, 0, v_fst_5112_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5122_, 1, v_snd_5113_);
                    v___x_5118_ = v_reuseFailAlloc_5122_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_5111_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_5110_, 0, v___x_5118_);
                    v___x_5120_ = v___x_5110_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_5121_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5121_, 0, v___x_5118_);
                    v___x_5120_ = v_reuseFailAlloc_5121_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_5120_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_RBMap_min___boxed(
    mut v_00_u03b1_5125_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_5126_: *mut crate::leanh::LeanObject,
    mut v_cmp_5127_: *mut crate::leanh::LeanObject,
    mut v_x_5128_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5129_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5129_ = l_Lean_RBMap_min(v_00_u03b1_5125_, v_00_u03b2_5126_, v_cmp_5127_, v_x_5128_);
    crate::leanh::lean_dec(v_x_5128_);
    crate::leanh::lean_dec_ref(v_cmp_5127_);
    return v_res_5129_;
}
pub unsafe fn l_Lean_RBMap_max___redArg(
    mut v_x_5130_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5131_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5132_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_5133_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5135_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5136_: u8 = 0;
    let mut v_fst_5137_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_5138_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5140_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5141_: u8 = 0;
    let mut v___x_5143_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5145_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5146_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5147_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5148_: u8 = 0;
    let mut v_isSharedCheck_5149_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5131_ = l_Lean_RBNode_max___redArg(v_x_5130_);
                if crate::leanh::lean_obj_tag(v___x_5131_) == 0 {
                    v___x_5132_ = crate::leanh::lean_box(0);
                    return v___x_5132_;
                } else {
                    v_val_5133_ = crate::leanh::lean_ctor_get(v___x_5131_, 0);
                    v_isSharedCheck_5149_ = (!crate::leanh::lean_is_exclusive(v___x_5131_)) as u8;
                    if v_isSharedCheck_5149_ == 0 {
                        v___x_5135_ = v___x_5131_;
                        v_isShared_5136_ = v_isSharedCheck_5149_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_val_5133_);
                        crate::leanh::lean_dec(v___x_5131_);
                        v___x_5135_ = crate::leanh::lean_box(0);
                        v_isShared_5136_ = v_isSharedCheck_5149_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v_fst_5137_ = crate::leanh::lean_ctor_get(v_val_5133_, 0);
                v_snd_5138_ = crate::leanh::lean_ctor_get(v_val_5133_, 1);
                v_isSharedCheck_5148_ = (!crate::leanh::lean_is_exclusive(v_val_5133_)) as u8;
                if v_isSharedCheck_5148_ == 0 {
                    v___x_5140_ = v_val_5133_;
                    v_isShared_5141_ = v_isSharedCheck_5148_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_snd_5138_);
                    crate::leanh::lean_inc(v_fst_5137_);
                    crate::leanh::lean_dec(v_val_5133_);
                    v___x_5140_ = crate::leanh::lean_box(0);
                    v_isShared_5141_ = v_isSharedCheck_5148_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                if v_isShared_5141_ == 0 {
                    v___x_5143_ = v___x_5140_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_5147_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5147_, 0, v_fst_5137_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5147_, 1, v_snd_5138_);
                    v___x_5143_ = v_reuseFailAlloc_5147_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_5136_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_5135_, 0, v___x_5143_);
                    v___x_5145_ = v___x_5135_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_5146_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5146_, 0, v___x_5143_);
                    v___x_5145_ = v_reuseFailAlloc_5146_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_5145_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_RBMap_max___redArg___boxed(
    mut v_x_5150_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5151_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5151_ = l_Lean_RBMap_max___redArg(v_x_5150_);
    crate::leanh::lean_dec(v_x_5150_);
    return v_res_5151_;
}
pub unsafe fn l_Lean_RBMap_max(
    mut v_00_u03b1_5152_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_5153_: *mut crate::leanh::LeanObject,
    mut v_cmp_5154_: *mut crate::leanh::LeanObject,
    mut v_x_5155_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5156_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5157_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_5158_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5160_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5161_: u8 = 0;
    let mut v_fst_5162_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_5163_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5165_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5166_: u8 = 0;
    let mut v___x_5168_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5170_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5171_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5172_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5173_: u8 = 0;
    let mut v_isSharedCheck_5174_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5156_ = l_Lean_RBNode_max___redArg(v_x_5155_);
                if crate::leanh::lean_obj_tag(v___x_5156_) == 0 {
                    v___x_5157_ = crate::leanh::lean_box(0);
                    return v___x_5157_;
                } else {
                    v_val_5158_ = crate::leanh::lean_ctor_get(v___x_5156_, 0);
                    v_isSharedCheck_5174_ = (!crate::leanh::lean_is_exclusive(v___x_5156_)) as u8;
                    if v_isSharedCheck_5174_ == 0 {
                        v___x_5160_ = v___x_5156_;
                        v_isShared_5161_ = v_isSharedCheck_5174_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_val_5158_);
                        crate::leanh::lean_dec(v___x_5156_);
                        v___x_5160_ = crate::leanh::lean_box(0);
                        v_isShared_5161_ = v_isSharedCheck_5174_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v_fst_5162_ = crate::leanh::lean_ctor_get(v_val_5158_, 0);
                v_snd_5163_ = crate::leanh::lean_ctor_get(v_val_5158_, 1);
                v_isSharedCheck_5173_ = (!crate::leanh::lean_is_exclusive(v_val_5158_)) as u8;
                if v_isSharedCheck_5173_ == 0 {
                    v___x_5165_ = v_val_5158_;
                    v_isShared_5166_ = v_isSharedCheck_5173_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_snd_5163_);
                    crate::leanh::lean_inc(v_fst_5162_);
                    crate::leanh::lean_dec(v_val_5158_);
                    v___x_5165_ = crate::leanh::lean_box(0);
                    v_isShared_5166_ = v_isSharedCheck_5173_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                if v_isShared_5166_ == 0 {
                    v___x_5168_ = v___x_5165_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_5172_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5172_, 0, v_fst_5162_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5172_, 1, v_snd_5163_);
                    v___x_5168_ = v_reuseFailAlloc_5172_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_5161_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_5160_, 0, v___x_5168_);
                    v___x_5170_ = v___x_5160_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_5171_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5171_, 0, v___x_5168_);
                    v___x_5170_ = v_reuseFailAlloc_5171_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_5170_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_RBMap_max___boxed(
    mut v_00_u03b1_5175_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_5176_: *mut crate::leanh::LeanObject,
    mut v_cmp_5177_: *mut crate::leanh::LeanObject,
    mut v_x_5178_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5179_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5179_ = l_Lean_RBMap_max(v_00_u03b1_5175_, v_00_u03b2_5176_, v_cmp_5177_, v_x_5178_);
    crate::leanh::lean_dec(v_x_5178_);
    crate::leanh::lean_dec_ref(v_cmp_5177_);
    return v_res_5179_;
}
pub unsafe fn l_Lean_RBMap_instRepr___redArg___lam__0(
    mut v___x_5183_: *mut crate::leanh::LeanObject,
    mut v_m_5184_: *mut crate::leanh::LeanObject,
    mut v_prec_5185_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5186_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5187_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5188_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5189_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5190_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5186_ = l_Lean_RBMap_instRepr___redArg___lam__0___closed__1;
    v___x_5187_ = l_Lean_RBMap_toList___redArg(v_m_5184_);
    v___x_5188_ = l_List_repr___redArg(v___x_5183_, v___x_5187_);
    v___x_5189_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_5189_, 0, v___x_5186_);
    crate::leanh::lean_ctor_set(v___x_5189_, 1, v___x_5188_);
    v___x_5190_ = l_Repr_addAppParen(v___x_5189_, v_prec_5185_);
    return v___x_5190_;
}
pub unsafe fn l_Lean_RBMap_instRepr___redArg___lam__0___boxed(
    mut v___x_5191_: *mut crate::leanh::LeanObject,
    mut v_m_5192_: *mut crate::leanh::LeanObject,
    mut v_prec_5193_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5194_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5194_ = l_Lean_RBMap_instRepr___redArg___lam__0(v___x_5191_, v_m_5192_, v_prec_5193_);
    crate::leanh::lean_dec(v_prec_5193_);
    return v_res_5194_;
}
pub unsafe fn l_Lean_RBMap_instRepr___redArg(
    mut v_inst_5195_: *mut crate::leanh::LeanObject,
    mut v_inst_5196_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_5197_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5198_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_5199_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_5197_ = crate::leanh::lean_alloc_closure(
        l_instReprTupleOfRepr___redArg___lam__0 as *mut core::ffi::c_void,
        3,
        1,
    );
    crate::leanh::lean_closure_set(v___f_5197_, 0, v_inst_5196_);
    v___x_5198_ =
        crate::leanh::lean_alloc_closure(l_Prod_repr___boxed as *mut core::ffi::c_void, 6, 4);
    crate::leanh::lean_closure_set(v___x_5198_, 0, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_5198_, 1, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_5198_, 2, v_inst_5195_);
    crate::leanh::lean_closure_set(v___x_5198_, 3, v___f_5197_);
    v___f_5199_ = crate::leanh::lean_alloc_closure(
        l_Lean_RBMap_instRepr___redArg___lam__0___boxed as *mut core::ffi::c_void,
        3,
        1,
    );
    crate::leanh::lean_closure_set(v___f_5199_, 0, v___x_5198_);
    return v___f_5199_;
}
pub unsafe fn l_Lean_RBMap_instRepr(
    mut v_00_u03b1_5200_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_5201_: *mut crate::leanh::LeanObject,
    mut v_cmp_5202_: *mut crate::leanh::LeanObject,
    mut v_inst_5203_: *mut crate::leanh::LeanObject,
    mut v_inst_5204_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5205_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5205_ = l_Lean_RBMap_instRepr___redArg(v_inst_5203_, v_inst_5204_);
    return v___x_5205_;
}
pub unsafe fn l_Lean_RBMap_instRepr___boxed(
    mut v_00_u03b1_5206_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_5207_: *mut crate::leanh::LeanObject,
    mut v_cmp_5208_: *mut crate::leanh::LeanObject,
    mut v_inst_5209_: *mut crate::leanh::LeanObject,
    mut v_inst_5210_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5211_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5211_ = l_Lean_RBMap_instRepr(
        v_00_u03b1_5206_,
        v_00_u03b2_5207_,
        v_cmp_5208_,
        v_inst_5209_,
        v_inst_5210_,
    );
    crate::leanh::lean_dec_ref(v_cmp_5208_);
    return v_res_5211_;
}
pub unsafe fn l_Lean_RBMap_insert___redArg(
    mut v_cmp_5212_: *mut crate::leanh::LeanObject,
    mut v_x_5213_: *mut crate::leanh::LeanObject,
    mut v_x_5214_: *mut crate::leanh::LeanObject,
    mut v_x_5215_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5216_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5216_ = l_Lean_RBNode_insert___redArg(v_cmp_5212_, v_x_5213_, v_x_5214_, v_x_5215_);
    return v___x_5216_;
}
pub unsafe fn l_Lean_RBMap_insert(
    mut v_00_u03b1_5217_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_5218_: *mut crate::leanh::LeanObject,
    mut v_cmp_5219_: *mut crate::leanh::LeanObject,
    mut v_x_5220_: *mut crate::leanh::LeanObject,
    mut v_x_5221_: *mut crate::leanh::LeanObject,
    mut v_x_5222_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5223_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5223_ = l_Lean_RBNode_insert___redArg(v_cmp_5219_, v_x_5220_, v_x_5221_, v_x_5222_);
    return v___x_5223_;
}
pub unsafe fn l_Lean_RBMap_erase___redArg(
    mut v_cmp_5224_: *mut crate::leanh::LeanObject,
    mut v_x_5225_: *mut crate::leanh::LeanObject,
    mut v_x_5226_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5227_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5227_ = l_Lean_RBNode_erase___redArg(v_cmp_5224_, v_x_5226_, v_x_5225_);
    return v___x_5227_;
}
pub unsafe fn l_Lean_RBMap_erase(
    mut v_00_u03b1_5228_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_5229_: *mut crate::leanh::LeanObject,
    mut v_cmp_5230_: *mut crate::leanh::LeanObject,
    mut v_x_5231_: *mut crate::leanh::LeanObject,
    mut v_x_5232_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5233_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5233_ = l_Lean_RBNode_erase___redArg(v_cmp_5230_, v_x_5232_, v_x_5231_);
    return v___x_5233_;
}
pub unsafe fn l_Lean_RBMap_ofList___redArg(
    mut v_cmp_5234_: *mut crate::leanh::LeanObject,
    mut v_x_5235_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_5235_) == 0 {
        let mut v___x_5236_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec_ref(v_cmp_5234_);
        v___x_5236_ = crate::leanh::lean_box(0);
        return v___x_5236_;
    } else {
        let mut v_head_5237_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_tail_5238_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_fst_5239_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_snd_5240_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_val_5241_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5242_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_head_5237_ = crate::leanh::lean_ctor_get(v_x_5235_, 0);
        crate::leanh::lean_inc(v_head_5237_);
        v_tail_5238_ = crate::leanh::lean_ctor_get(v_x_5235_, 1);
        crate::leanh::lean_inc(v_tail_5238_);
        crate::leanh::lean_dec_ref_known(v_x_5235_, 2);
        v_fst_5239_ = crate::leanh::lean_ctor_get(v_head_5237_, 0);
        crate::leanh::lean_inc(v_fst_5239_);
        v_snd_5240_ = crate::leanh::lean_ctor_get(v_head_5237_, 1);
        crate::leanh::lean_inc(v_snd_5240_);
        crate::leanh::lean_dec(v_head_5237_);
        crate::leanh::lean_inc_ref(v_cmp_5234_);
        v_val_5241_ = l_Lean_RBMap_ofList___redArg(v_cmp_5234_, v_tail_5238_);
        v___x_5242_ =
            l_Lean_RBNode_insert___redArg(v_cmp_5234_, v_val_5241_, v_fst_5239_, v_snd_5240_);
        return v___x_5242_;
    }
}
pub unsafe fn l_Lean_RBMap_ofList(
    mut v_00_u03b1_5243_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_5244_: *mut crate::leanh::LeanObject,
    mut v_cmp_5245_: *mut crate::leanh::LeanObject,
    mut v_x_5246_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5247_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5247_ = l_Lean_RBMap_ofList___redArg(v_cmp_5245_, v_x_5246_);
    return v___x_5247_;
}
pub unsafe fn l_Lean_RBMap_findCore_x3f___redArg(
    mut v_cmp_5248_: *mut crate::leanh::LeanObject,
    mut v_x_5249_: *mut crate::leanh::LeanObject,
    mut v_x_5250_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5251_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5251_ = l_Lean_RBNode_findCore___redArg(v_cmp_5248_, v_x_5249_, v_x_5250_);
    return v___x_5251_;
}
pub unsafe fn l_Lean_RBMap_findCore_x3f(
    mut v_00_u03b1_5252_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_5253_: *mut crate::leanh::LeanObject,
    mut v_cmp_5254_: *mut crate::leanh::LeanObject,
    mut v_x_5255_: *mut crate::leanh::LeanObject,
    mut v_x_5256_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5257_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5257_ = l_Lean_RBNode_findCore___redArg(v_cmp_5254_, v_x_5255_, v_x_5256_);
    return v___x_5257_;
}
pub unsafe fn l_Lean_RBMap_find_x3f___redArg(
    mut v_cmp_5258_: *mut crate::leanh::LeanObject,
    mut v_x_5259_: *mut crate::leanh::LeanObject,
    mut v_x_5260_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5261_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5261_ = l_Lean_RBNode_find___redArg(v_cmp_5258_, v_x_5259_, v_x_5260_);
    return v___x_5261_;
}
pub unsafe fn l_Lean_RBMap_find_x3f(
    mut v_00_u03b1_5262_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_5263_: *mut crate::leanh::LeanObject,
    mut v_cmp_5264_: *mut crate::leanh::LeanObject,
    mut v_x_5265_: *mut crate::leanh::LeanObject,
    mut v_x_5266_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5267_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5267_ = l_Lean_RBNode_find___redArg(v_cmp_5264_, v_x_5265_, v_x_5266_);
    return v___x_5267_;
}
pub unsafe fn l_Lean_RBMap_findD___redArg(
    mut v_cmp_5268_: *mut crate::leanh::LeanObject,
    mut v_t_5269_: *mut crate::leanh::LeanObject,
    mut v_k_5270_: *mut crate::leanh::LeanObject,
    mut v_v_u2080_5271_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5272_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5272_ = l_Lean_RBNode_find___redArg(v_cmp_5268_, v_t_5269_, v_k_5270_);
    if crate::leanh::lean_obj_tag(v___x_5272_) == 0 {
        crate::leanh::lean_inc(v_v_u2080_5271_);
        return v_v_u2080_5271_;
    } else {
        let mut v_val_5273_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_val_5273_ = crate::leanh::lean_ctor_get(v___x_5272_, 0);
        crate::leanh::lean_inc(v_val_5273_);
        crate::leanh::lean_dec_ref_known(v___x_5272_, 1);
        return v_val_5273_;
    }
}
pub unsafe fn l_Lean_RBMap_findD___redArg___boxed(
    mut v_cmp_5274_: *mut crate::leanh::LeanObject,
    mut v_t_5275_: *mut crate::leanh::LeanObject,
    mut v_k_5276_: *mut crate::leanh::LeanObject,
    mut v_v_u2080_5277_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5278_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5278_ = l_Lean_RBMap_findD___redArg(v_cmp_5274_, v_t_5275_, v_k_5276_, v_v_u2080_5277_);
    crate::leanh::lean_dec(v_v_u2080_5277_);
    return v_res_5278_;
}
pub unsafe fn l_Lean_RBMap_findD(
    mut v_00_u03b1_5279_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_5280_: *mut crate::leanh::LeanObject,
    mut v_cmp_5281_: *mut crate::leanh::LeanObject,
    mut v_t_5282_: *mut crate::leanh::LeanObject,
    mut v_k_5283_: *mut crate::leanh::LeanObject,
    mut v_v_u2080_5284_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5285_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5285_ = l_Lean_RBNode_find___redArg(v_cmp_5281_, v_t_5282_, v_k_5283_);
    if crate::leanh::lean_obj_tag(v___x_5285_) == 0 {
        crate::leanh::lean_inc(v_v_u2080_5284_);
        return v_v_u2080_5284_;
    } else {
        let mut v_val_5286_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_val_5286_ = crate::leanh::lean_ctor_get(v___x_5285_, 0);
        crate::leanh::lean_inc(v_val_5286_);
        crate::leanh::lean_dec_ref_known(v___x_5285_, 1);
        return v_val_5286_;
    }
}
pub unsafe fn l_Lean_RBMap_findD___boxed(
    mut v_00_u03b1_5287_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_5288_: *mut crate::leanh::LeanObject,
    mut v_cmp_5289_: *mut crate::leanh::LeanObject,
    mut v_t_5290_: *mut crate::leanh::LeanObject,
    mut v_k_5291_: *mut crate::leanh::LeanObject,
    mut v_v_u2080_5292_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5293_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5293_ = l_Lean_RBMap_findD(
        v_00_u03b1_5287_,
        v_00_u03b2_5288_,
        v_cmp_5289_,
        v_t_5290_,
        v_k_5291_,
        v_v_u2080_5292_,
    );
    crate::leanh::lean_dec(v_v_u2080_5292_);
    return v_res_5293_;
}
pub unsafe fn l_Lean_RBMap_lowerBound___redArg(
    mut v_cmp_5294_: *mut crate::leanh::LeanObject,
    mut v_x_5295_: *mut crate::leanh::LeanObject,
    mut v_x_5296_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5297_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5298_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5297_ = crate::leanh::lean_box(0);
    v___x_5298_ = l_Lean_RBNode_lowerBound___redArg(v_cmp_5294_, v_x_5295_, v_x_5296_, v___x_5297_);
    return v___x_5298_;
}
pub unsafe fn l_Lean_RBMap_lowerBound(
    mut v_00_u03b1_5299_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_5300_: *mut crate::leanh::LeanObject,
    mut v_cmp_5301_: *mut crate::leanh::LeanObject,
    mut v_x_5302_: *mut crate::leanh::LeanObject,
    mut v_x_5303_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5304_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5305_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5304_ = crate::leanh::lean_box(0);
    v___x_5305_ = l_Lean_RBNode_lowerBound___redArg(v_cmp_5301_, v_x_5302_, v_x_5303_, v___x_5304_);
    return v___x_5305_;
}
pub unsafe fn l_Lean_RBMap_contains___redArg(
    mut v_cmp_5306_: *mut crate::leanh::LeanObject,
    mut v_t_5307_: *mut crate::leanh::LeanObject,
    mut v_a_5308_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_5309_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5309_ = l_Lean_RBNode_find___redArg(v_cmp_5306_, v_t_5307_, v_a_5308_);
    if crate::leanh::lean_obj_tag(v___x_5309_) == 0 {
        let mut v___x_5310_: u8 = 0;
        v___x_5310_ = 0;
        return v___x_5310_;
    } else {
        let mut v___x_5311_: u8 = 0;
        crate::leanh::lean_dec_ref_known(v___x_5309_, 1);
        v___x_5311_ = 1;
        return v___x_5311_;
    }
}
pub unsafe fn l_Lean_RBMap_contains___redArg___boxed(
    mut v_cmp_5312_: *mut crate::leanh::LeanObject,
    mut v_t_5313_: *mut crate::leanh::LeanObject,
    mut v_a_5314_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5315_: u8 = 0;
    let mut v_r_5316_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5315_ = l_Lean_RBMap_contains___redArg(v_cmp_5312_, v_t_5313_, v_a_5314_);
    v_r_5316_ = crate::leanh::lean_box((v_res_5315_) as usize);
    return v_r_5316_;
}
pub unsafe fn l_Lean_RBMap_contains(
    mut v_00_u03b1_5317_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_5318_: *mut crate::leanh::LeanObject,
    mut v_cmp_5319_: *mut crate::leanh::LeanObject,
    mut v_t_5320_: *mut crate::leanh::LeanObject,
    mut v_a_5321_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_5322_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5322_ = l_Lean_RBNode_find___redArg(v_cmp_5319_, v_t_5320_, v_a_5321_);
    if crate::leanh::lean_obj_tag(v___x_5322_) == 0 {
        let mut v___x_5323_: u8 = 0;
        v___x_5323_ = 0;
        return v___x_5323_;
    } else {
        let mut v___x_5324_: u8 = 0;
        crate::leanh::lean_dec_ref_known(v___x_5322_, 1);
        v___x_5324_ = 1;
        return v___x_5324_;
    }
}
pub unsafe fn l_Lean_RBMap_contains___boxed(
    mut v_00_u03b1_5325_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_5326_: *mut crate::leanh::LeanObject,
    mut v_cmp_5327_: *mut crate::leanh::LeanObject,
    mut v_t_5328_: *mut crate::leanh::LeanObject,
    mut v_a_5329_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5330_: u8 = 0;
    let mut v_r_5331_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5330_ = l_Lean_RBMap_contains(
        v_00_u03b1_5325_,
        v_00_u03b2_5326_,
        v_cmp_5327_,
        v_t_5328_,
        v_a_5329_,
    );
    v_r_5331_ = crate::leanh::lean_box((v_res_5330_) as usize);
    return v_r_5331_;
}
pub unsafe fn l_Lean_RBMap_fromList___redArg___lam__0(
    mut v_cmp_5332_: *mut crate::leanh::LeanObject,
    mut v_r_5333_: *mut crate::leanh::LeanObject,
    mut v_p_5334_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_fst_5335_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_5336_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5337_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_fst_5335_ = crate::leanh::lean_ctor_get(v_p_5334_, 0);
    crate::leanh::lean_inc(v_fst_5335_);
    v_snd_5336_ = crate::leanh::lean_ctor_get(v_p_5334_, 1);
    crate::leanh::lean_inc(v_snd_5336_);
    crate::leanh::lean_dec_ref(v_p_5334_);
    v___x_5337_ = l_Lean_RBNode_insert___redArg(v_cmp_5332_, v_r_5333_, v_fst_5335_, v_snd_5336_);
    return v___x_5337_;
}
pub unsafe fn l_Lean_RBMap_fromList___redArg(
    mut v_l_5338_: *mut crate::leanh::LeanObject,
    mut v_cmp_5339_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_5340_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5341_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5342_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_5340_ = crate::leanh::lean_alloc_closure(
        l_Lean_RBMap_fromList___redArg___lam__0 as *mut core::ffi::c_void,
        3,
        1,
    );
    crate::leanh::lean_closure_set(v___f_5340_, 0, v_cmp_5339_);
    v___x_5341_ = crate::leanh::lean_box(0);
    v___x_5342_ = l_List_foldl___redArg(v___f_5340_, v___x_5341_, v_l_5338_);
    return v___x_5342_;
}
pub unsafe fn l_Lean_RBMap_fromList(
    mut v_00_u03b1_5343_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_5344_: *mut crate::leanh::LeanObject,
    mut v_l_5345_: *mut crate::leanh::LeanObject,
    mut v_cmp_5346_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_5347_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5348_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5349_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_5347_ = crate::leanh::lean_alloc_closure(
        l_Lean_RBMap_fromList___redArg___lam__0 as *mut core::ffi::c_void,
        3,
        1,
    );
    crate::leanh::lean_closure_set(v___f_5347_, 0, v_cmp_5346_);
    v___x_5348_ = crate::leanh::lean_box(0);
    v___x_5349_ = l_List_foldl___redArg(v___f_5347_, v___x_5348_, v_l_5345_);
    return v___x_5349_;
}
pub unsafe fn l_Lean_RBMap_fromArray___redArg___lam__0(
    mut v_cmp_5350_: *mut crate::leanh::LeanObject,
    mut v_x1_5351_: *mut crate::leanh::LeanObject,
    mut v_x2_5352_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_fst_5353_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_5354_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5355_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_fst_5353_ = crate::leanh::lean_ctor_get(v_x2_5352_, 0);
    crate::leanh::lean_inc(v_fst_5353_);
    v_snd_5354_ = crate::leanh::lean_ctor_get(v_x2_5352_, 1);
    crate::leanh::lean_inc(v_snd_5354_);
    crate::leanh::lean_dec_ref(v_x2_5352_);
    v___x_5355_ = l_Lean_RBNode_insert___redArg(v_cmp_5350_, v_x1_5351_, v_fst_5353_, v_snd_5354_);
    return v___x_5355_;
}
pub unsafe fn l_Lean_RBMap_fromArray___redArg(
    mut v_l_5375_: *mut crate::leanh::LeanObject,
    mut v_cmp_5376_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5377_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5378_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5379_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5380_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5381_: u8 = 0;
    v___x_5377_ = crate::leanh::lean_box(0);
    v___x_5378_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_5379_ = lean_array_get_size(v_l_5375_);
    v___x_5380_ = l_Lean_RBMap_fromArray___redArg___closed__9;
    v___x_5381_ = lean_nat_dec_lt(v___x_5378_, v___x_5379_);
    if v___x_5381_ == 0 {
        crate::leanh::lean_dec_ref(v_cmp_5376_);
        crate::leanh::lean_dec_ref(v_l_5375_);
        return v___x_5377_;
    } else {
        let mut v___f_5382_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5383_: u8 = 0;
        v___f_5382_ = crate::leanh::lean_alloc_closure(
            l_Lean_RBMap_fromArray___redArg___lam__0 as *mut core::ffi::c_void,
            3,
            1,
        );
        crate::leanh::lean_closure_set(v___f_5382_, 0, v_cmp_5376_);
        v___x_5383_ = lean_nat_dec_le(v___x_5379_, v___x_5379_);
        if v___x_5383_ == 0 {
            if v___x_5381_ == 0 {
                crate::leanh::lean_dec_ref(v___f_5382_);
                crate::leanh::lean_dec_ref(v_l_5375_);
                return v___x_5377_;
            } else {
                let mut v___x_5384_: usize = 0;
                let mut v___x_5385_: usize = 0;
                let mut v___x_5386_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                v___x_5384_ = 0usize;
                v___x_5385_ = lean_usize_of_nat(v___x_5379_);
                v___x_5386_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(
                    crate::leanh::lean_box(0),
                    crate::leanh::lean_box(0),
                    crate::leanh::lean_box(0),
                    v___x_5380_,
                    v___f_5382_,
                    v_l_5375_,
                    v___x_5384_,
                    v___x_5385_,
                    v___x_5377_,
                );
                return v___x_5386_;
            }
        } else {
            let mut v___x_5387_: usize = 0;
            let mut v___x_5388_: usize = 0;
            let mut v___x_5389_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_5387_ = 0usize;
            v___x_5388_ = lean_usize_of_nat(v___x_5379_);
            v___x_5389_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(
                crate::leanh::lean_box(0),
                crate::leanh::lean_box(0),
                crate::leanh::lean_box(0),
                v___x_5380_,
                v___f_5382_,
                v_l_5375_,
                v___x_5387_,
                v___x_5388_,
                v___x_5377_,
            );
            return v___x_5389_;
        }
    }
}
pub unsafe fn l_Lean_RBMap_fromArray(
    mut v_00_u03b1_5390_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_5391_: *mut crate::leanh::LeanObject,
    mut v_l_5392_: *mut crate::leanh::LeanObject,
    mut v_cmp_5393_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5394_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5395_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5396_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5397_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5398_: u8 = 0;
    v___x_5394_ = crate::leanh::lean_box(0);
    v___x_5395_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_5396_ = lean_array_get_size(v_l_5392_);
    v___x_5397_ = l_Lean_RBMap_fromArray___redArg___closed__9;
    v___x_5398_ = lean_nat_dec_lt(v___x_5395_, v___x_5396_);
    if v___x_5398_ == 0 {
        crate::leanh::lean_dec_ref(v_cmp_5393_);
        crate::leanh::lean_dec_ref(v_l_5392_);
        return v___x_5394_;
    } else {
        let mut v___f_5399_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5400_: u8 = 0;
        v___f_5399_ = crate::leanh::lean_alloc_closure(
            l_Lean_RBMap_fromArray___redArg___lam__0 as *mut core::ffi::c_void,
            3,
            1,
        );
        crate::leanh::lean_closure_set(v___f_5399_, 0, v_cmp_5393_);
        v___x_5400_ = lean_nat_dec_le(v___x_5396_, v___x_5396_);
        if v___x_5400_ == 0 {
            if v___x_5398_ == 0 {
                crate::leanh::lean_dec_ref(v___f_5399_);
                crate::leanh::lean_dec_ref(v_l_5392_);
                return v___x_5394_;
            } else {
                let mut v___x_5401_: usize = 0;
                let mut v___x_5402_: usize = 0;
                let mut v___x_5403_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                v___x_5401_ = 0usize;
                v___x_5402_ = lean_usize_of_nat(v___x_5396_);
                v___x_5403_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(
                    crate::leanh::lean_box(0),
                    crate::leanh::lean_box(0),
                    crate::leanh::lean_box(0),
                    v___x_5397_,
                    v___f_5399_,
                    v_l_5392_,
                    v___x_5401_,
                    v___x_5402_,
                    v___x_5394_,
                );
                return v___x_5403_;
            }
        } else {
            let mut v___x_5404_: usize = 0;
            let mut v___x_5405_: usize = 0;
            let mut v___x_5406_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_5404_ = 0usize;
            v___x_5405_ = lean_usize_of_nat(v___x_5396_);
            v___x_5406_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(
                crate::leanh::lean_box(0),
                crate::leanh::lean_box(0),
                crate::leanh::lean_box(0),
                v___x_5397_,
                v___f_5399_,
                v_l_5392_,
                v___x_5404_,
                v___x_5405_,
                v___x_5394_,
            );
            return v___x_5406_;
        }
    }
}
pub unsafe fn l_Lean_RBMap_all___redArg(
    mut v_x_5407_: *mut crate::leanh::LeanObject,
    mut v_x_5408_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_5409_: u8 = 0;
    v___x_5409_ = l_Lean_RBNode_all___redArg(v_x_5408_, v_x_5407_);
    return v___x_5409_;
}
pub unsafe fn l_Lean_RBMap_all___redArg___boxed(
    mut v_x_5410_: *mut crate::leanh::LeanObject,
    mut v_x_5411_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5412_: u8 = 0;
    let mut v_r_5413_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5412_ = l_Lean_RBMap_all___redArg(v_x_5410_, v_x_5411_);
    v_r_5413_ = crate::leanh::lean_box((v_res_5412_) as usize);
    return v_r_5413_;
}
pub unsafe fn l_Lean_RBMap_all(
    mut v_00_u03b1_5414_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_5415_: *mut crate::leanh::LeanObject,
    mut v_cmp_5416_: *mut crate::leanh::LeanObject,
    mut v_x_5417_: *mut crate::leanh::LeanObject,
    mut v_x_5418_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_5419_: u8 = 0;
    v___x_5419_ = l_Lean_RBNode_all___redArg(v_x_5418_, v_x_5417_);
    return v___x_5419_;
}
pub unsafe fn l_Lean_RBMap_all___boxed(
    mut v_00_u03b1_5420_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_5421_: *mut crate::leanh::LeanObject,
    mut v_cmp_5422_: *mut crate::leanh::LeanObject,
    mut v_x_5423_: *mut crate::leanh::LeanObject,
    mut v_x_5424_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5425_: u8 = 0;
    let mut v_r_5426_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5425_ = l_Lean_RBMap_all(
        v_00_u03b1_5420_,
        v_00_u03b2_5421_,
        v_cmp_5422_,
        v_x_5423_,
        v_x_5424_,
    );
    crate::leanh::lean_dec_ref(v_cmp_5422_);
    v_r_5426_ = crate::leanh::lean_box((v_res_5425_) as usize);
    return v_r_5426_;
}
pub unsafe fn l_Lean_RBMap_any___redArg(
    mut v_x_5427_: *mut crate::leanh::LeanObject,
    mut v_x_5428_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_5429_: u8 = 0;
    v___x_5429_ = l_Lean_RBNode_any___redArg(v_x_5428_, v_x_5427_);
    return v___x_5429_;
}
pub unsafe fn l_Lean_RBMap_any___redArg___boxed(
    mut v_x_5430_: *mut crate::leanh::LeanObject,
    mut v_x_5431_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5432_: u8 = 0;
    let mut v_r_5433_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5432_ = l_Lean_RBMap_any___redArg(v_x_5430_, v_x_5431_);
    v_r_5433_ = crate::leanh::lean_box((v_res_5432_) as usize);
    return v_r_5433_;
}
pub unsafe fn l_Lean_RBMap_any(
    mut v_00_u03b1_5434_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_5435_: *mut crate::leanh::LeanObject,
    mut v_cmp_5436_: *mut crate::leanh::LeanObject,
    mut v_x_5437_: *mut crate::leanh::LeanObject,
    mut v_x_5438_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_5439_: u8 = 0;
    v___x_5439_ = l_Lean_RBNode_any___redArg(v_x_5438_, v_x_5437_);
    return v___x_5439_;
}
pub unsafe fn l_Lean_RBMap_any___boxed(
    mut v_00_u03b1_5440_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_5441_: *mut crate::leanh::LeanObject,
    mut v_cmp_5442_: *mut crate::leanh::LeanObject,
    mut v_x_5443_: *mut crate::leanh::LeanObject,
    mut v_x_5444_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5445_: u8 = 0;
    let mut v_r_5446_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5445_ = l_Lean_RBMap_any(
        v_00_u03b1_5440_,
        v_00_u03b2_5441_,
        v_cmp_5442_,
        v_x_5443_,
        v_x_5444_,
    );
    crate::leanh::lean_dec_ref(v_cmp_5442_);
    v_r_5446_ = crate::leanh::lean_box((v_res_5445_) as usize);
    return v_r_5446_;
}
pub unsafe fn l_Lean_RBNode_fold___at___00Lean_RBMap_size_spec__0___redArg(
    mut v_x_5447_: *mut crate::leanh::LeanObject,
    mut v_x_5448_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_lchild_5449_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_rchild_5450_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5451_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5452_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5453_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_5448_) == 0 {
                    return v_x_5447_;
                } else {
                    v_lchild_5449_ = crate::leanh::lean_ctor_get(v_x_5448_, 0);
                    v_rchild_5450_ = crate::leanh::lean_ctor_get(v_x_5448_, 3);
                    v___x_5451_ = l_Lean_RBNode_fold___at___00Lean_RBMap_size_spec__0___redArg(
                        v_x_5447_,
                        v_lchild_5449_,
                    );
                    v___x_5452_ = crate::leanh::lean_unsigned_to_nat(1);
                    v___x_5453_ = lean_nat_add(v___x_5451_, v___x_5452_);
                    crate::leanh::lean_dec(v___x_5451_);
                    v_x_5447_ = v___x_5453_;
                    v_x_5448_ = v_rchild_5450_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_RBNode_fold___at___00Lean_RBMap_size_spec__0___redArg___boxed(
    mut v_x_5455_: *mut crate::leanh::LeanObject,
    mut v_x_5456_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5457_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5457_ =
        l_Lean_RBNode_fold___at___00Lean_RBMap_size_spec__0___redArg(v_x_5455_, v_x_5456_);
    crate::leanh::lean_dec(v_x_5456_);
    return v_res_5457_;
}
pub unsafe fn l_Lean_RBMap_size___redArg(
    mut v_m_5458_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5459_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5460_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5459_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_5460_ =
        l_Lean_RBNode_fold___at___00Lean_RBMap_size_spec__0___redArg(v___x_5459_, v_m_5458_);
    return v___x_5460_;
}
pub unsafe fn l_Lean_RBMap_size___redArg___boxed(
    mut v_m_5461_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5462_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5462_ = l_Lean_RBMap_size___redArg(v_m_5461_);
    crate::leanh::lean_dec(v_m_5461_);
    return v_res_5462_;
}
pub unsafe fn l_Lean_RBMap_size(
    mut v_00_u03b1_5463_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_5464_: *mut crate::leanh::LeanObject,
    mut v_cmp_5465_: *mut crate::leanh::LeanObject,
    mut v_m_5466_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5467_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5467_ = l_Lean_RBMap_size___redArg(v_m_5466_);
    return v___x_5467_;
}
pub unsafe fn l_Lean_RBMap_size___boxed(
    mut v_00_u03b1_5468_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_5469_: *mut crate::leanh::LeanObject,
    mut v_cmp_5470_: *mut crate::leanh::LeanObject,
    mut v_m_5471_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5472_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5472_ = l_Lean_RBMap_size(v_00_u03b1_5468_, v_00_u03b2_5469_, v_cmp_5470_, v_m_5471_);
    crate::leanh::lean_dec(v_m_5471_);
    crate::leanh::lean_dec_ref(v_cmp_5470_);
    return v_res_5472_;
}
pub unsafe fn l_Lean_RBNode_fold___at___00Lean_RBMap_size_spec__0(
    mut v_00_u03b1_5473_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_5474_: *mut crate::leanh::LeanObject,
    mut v_x_5475_: *mut crate::leanh::LeanObject,
    mut v_x_5476_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5477_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5477_ =
        l_Lean_RBNode_fold___at___00Lean_RBMap_size_spec__0___redArg(v_x_5475_, v_x_5476_);
    return v___x_5477_;
}
pub unsafe fn l_Lean_RBNode_fold___at___00Lean_RBMap_size_spec__0___boxed(
    mut v_00_u03b1_5478_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_5479_: *mut crate::leanh::LeanObject,
    mut v_x_5480_: *mut crate::leanh::LeanObject,
    mut v_x_5481_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5482_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5482_ = l_Lean_RBNode_fold___at___00Lean_RBMap_size_spec__0(
        v_00_u03b1_5478_,
        v_00_u03b2_5479_,
        v_x_5480_,
        v_x_5481_,
    );
    crate::leanh::lean_dec(v_x_5481_);
    return v_res_5482_;
}
pub unsafe fn l_Lean_RBMap_maxDepth___redArg___lam__0(
    mut v___y_5483_: *mut crate::leanh::LeanObject,
    mut v___y_5484_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5485_: u8 = 0;
    v___x_5485_ = lean_nat_dec_le(v___y_5483_, v___y_5484_);
    if v___x_5485_ == 0 {
        crate::leanh::lean_inc(v___y_5483_);
        return v___y_5483_;
    } else {
        crate::leanh::lean_inc(v___y_5484_);
        return v___y_5484_;
    }
}
pub unsafe fn l_Lean_RBMap_maxDepth___redArg___lam__0___boxed(
    mut v___y_5486_: *mut crate::leanh::LeanObject,
    mut v___y_5487_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5488_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5488_ = l_Lean_RBMap_maxDepth___redArg___lam__0(v___y_5486_, v___y_5487_);
    crate::leanh::lean_dec(v___y_5487_);
    crate::leanh::lean_dec(v___y_5486_);
    return v_res_5488_;
}
pub unsafe fn l_Lean_RBMap_maxDepth___redArg(
    mut v_t_5490_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_5491_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5492_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_5491_ = l_Lean_RBMap_maxDepth___redArg___closed__0;
    v___x_5492_ = l_Lean_RBNode_depth___redArg(v___f_5491_, v_t_5490_);
    return v___x_5492_;
}
pub unsafe fn l_Lean_RBMap_maxDepth___redArg___boxed(
    mut v_t_5493_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5494_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5494_ = l_Lean_RBMap_maxDepth___redArg(v_t_5493_);
    crate::leanh::lean_dec(v_t_5493_);
    return v_res_5494_;
}
pub unsafe fn l_Lean_RBMap_maxDepth(
    mut v_00_u03b1_5495_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_5496_: *mut crate::leanh::LeanObject,
    mut v_cmp_5497_: *mut crate::leanh::LeanObject,
    mut v_t_5498_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5499_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5499_ = l_Lean_RBMap_maxDepth___redArg(v_t_5498_);
    return v___x_5499_;
}
pub unsafe fn l_Lean_RBMap_maxDepth___boxed(
    mut v_00_u03b1_5500_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_5501_: *mut crate::leanh::LeanObject,
    mut v_cmp_5502_: *mut crate::leanh::LeanObject,
    mut v_t_5503_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5504_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5504_ = l_Lean_RBMap_maxDepth(v_00_u03b1_5500_, v_00_u03b2_5501_, v_cmp_5502_, v_t_5503_);
    crate::leanh::lean_dec(v_t_5503_);
    crate::leanh::lean_dec_ref(v_cmp_5502_);
    return v_res_5504_;
}
pub unsafe fn _init_l_Lean_RBMap_min_x21___redArg___closed__3() -> *mut crate::leanh::LeanObject {
    let mut v___x_5508_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5509_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5510_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5511_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5512_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5513_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5508_ = l_Lean_RBMap_min_x21___redArg___closed__2;
    v___x_5509_ = crate::leanh::lean_unsigned_to_nat(14);
    v___x_5510_ = crate::leanh::lean_unsigned_to_nat(384);
    v___x_5511_ = l_Lean_RBMap_min_x21___redArg___closed__1;
    v___x_5512_ = l_Lean_RBMap_min_x21___redArg___closed__0;
    v___x_5513_ = l_mkPanicMessageWithDecl(
        v___x_5512_,
        v___x_5511_,
        v___x_5510_,
        v___x_5509_,
        v___x_5508_,
    );
    return v___x_5513_;
}
pub unsafe fn l_Lean_RBMap_min_x21___redArg(
    mut v_inst_5514_: *mut crate::leanh::LeanObject,
    mut v_inst_5515_: *mut crate::leanh::LeanObject,
    mut v_t_5516_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5517_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5518_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5519_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5520_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_5521_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_5522_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_5523_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5525_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5526_: u8 = 0;
    let mut v___x_5528_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5529_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5530_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5517_ = l_Lean_RBNode_min___redArg(v_t_5516_);
                if crate::leanh::lean_obj_tag(v___x_5517_) == 0 {
                    v___x_5518_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_5518_, 0, v_inst_5514_);
                    crate::leanh::lean_ctor_set(v___x_5518_, 1, v_inst_5515_);
                    v___x_5519_ = crate::leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(l_Lean_RBMap_min_x21___redArg___closed__3),
                        core::ptr::addr_of_mut!(l_Lean_RBMap_min_x21___redArg___closed__3_once),
                        _init_l_Lean_RBMap_min_x21___redArg___closed__3,
                    );
                    v___x_5520_ = l_panic___redArg(v___x_5518_, v___x_5519_);
                    crate::leanh::lean_dec_ref_known(v___x_5518_, 2);
                    return v___x_5520_;
                } else {
                    crate::leanh::lean_dec(v_inst_5515_);
                    crate::leanh::lean_dec(v_inst_5514_);
                    v_val_5521_ = crate::leanh::lean_ctor_get(v___x_5517_, 0);
                    crate::leanh::lean_inc(v_val_5521_);
                    crate::leanh::lean_dec_ref_known(v___x_5517_, 1);
                    v_fst_5522_ = crate::leanh::lean_ctor_get(v_val_5521_, 0);
                    v_snd_5523_ = crate::leanh::lean_ctor_get(v_val_5521_, 1);
                    v_isSharedCheck_5530_ = (!crate::leanh::lean_is_exclusive(v_val_5521_)) as u8;
                    if v_isSharedCheck_5530_ == 0 {
                        v___x_5525_ = v_val_5521_;
                        v_isShared_5526_ = v_isSharedCheck_5530_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_snd_5523_);
                        crate::leanh::lean_inc(v_fst_5522_);
                        crate::leanh::lean_dec(v_val_5521_);
                        v___x_5525_ = crate::leanh::lean_box(0);
                        v_isShared_5526_ = v_isSharedCheck_5530_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_5526_ == 0 {
                    v___x_5528_ = v___x_5525_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_5529_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5529_, 0, v_fst_5522_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5529_, 1, v_snd_5523_);
                    v___x_5528_ = v_reuseFailAlloc_5529_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_5528_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_RBMap_min_x21___redArg___boxed(
    mut v_inst_5531_: *mut crate::leanh::LeanObject,
    mut v_inst_5532_: *mut crate::leanh::LeanObject,
    mut v_t_5533_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5534_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5534_ = l_Lean_RBMap_min_x21___redArg(v_inst_5531_, v_inst_5532_, v_t_5533_);
    crate::leanh::lean_dec(v_t_5533_);
    return v_res_5534_;
}
pub unsafe fn l_Lean_RBMap_min_x21(
    mut v_00_u03b1_5535_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_5536_: *mut crate::leanh::LeanObject,
    mut v_cmp_5537_: *mut crate::leanh::LeanObject,
    mut v_inst_5538_: *mut crate::leanh::LeanObject,
    mut v_inst_5539_: *mut crate::leanh::LeanObject,
    mut v_t_5540_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5541_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5542_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5543_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5544_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_5545_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_5546_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_5547_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5549_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5550_: u8 = 0;
    let mut v___x_5552_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5553_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5554_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5541_ = l_Lean_RBNode_min___redArg(v_t_5540_);
                if crate::leanh::lean_obj_tag(v___x_5541_) == 0 {
                    v___x_5542_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_5542_, 0, v_inst_5538_);
                    crate::leanh::lean_ctor_set(v___x_5542_, 1, v_inst_5539_);
                    v___x_5543_ = crate::leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(l_Lean_RBMap_min_x21___redArg___closed__3),
                        core::ptr::addr_of_mut!(l_Lean_RBMap_min_x21___redArg___closed__3_once),
                        _init_l_Lean_RBMap_min_x21___redArg___closed__3,
                    );
                    v___x_5544_ = l_panic___redArg(v___x_5542_, v___x_5543_);
                    crate::leanh::lean_dec_ref_known(v___x_5542_, 2);
                    return v___x_5544_;
                } else {
                    crate::leanh::lean_dec(v_inst_5539_);
                    crate::leanh::lean_dec(v_inst_5538_);
                    v_val_5545_ = crate::leanh::lean_ctor_get(v___x_5541_, 0);
                    crate::leanh::lean_inc(v_val_5545_);
                    crate::leanh::lean_dec_ref_known(v___x_5541_, 1);
                    v_fst_5546_ = crate::leanh::lean_ctor_get(v_val_5545_, 0);
                    v_snd_5547_ = crate::leanh::lean_ctor_get(v_val_5545_, 1);
                    v_isSharedCheck_5554_ = (!crate::leanh::lean_is_exclusive(v_val_5545_)) as u8;
                    if v_isSharedCheck_5554_ == 0 {
                        v___x_5549_ = v_val_5545_;
                        v_isShared_5550_ = v_isSharedCheck_5554_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_snd_5547_);
                        crate::leanh::lean_inc(v_fst_5546_);
                        crate::leanh::lean_dec(v_val_5545_);
                        v___x_5549_ = crate::leanh::lean_box(0);
                        v_isShared_5550_ = v_isSharedCheck_5554_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_5550_ == 0 {
                    v___x_5552_ = v___x_5549_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_5553_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5553_, 0, v_fst_5546_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5553_, 1, v_snd_5547_);
                    v___x_5552_ = v_reuseFailAlloc_5553_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_5552_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_RBMap_min_x21___boxed(
    mut v_00_u03b1_5555_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_5556_: *mut crate::leanh::LeanObject,
    mut v_cmp_5557_: *mut crate::leanh::LeanObject,
    mut v_inst_5558_: *mut crate::leanh::LeanObject,
    mut v_inst_5559_: *mut crate::leanh::LeanObject,
    mut v_t_5560_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5561_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5561_ = l_Lean_RBMap_min_x21(
        v_00_u03b1_5555_,
        v_00_u03b2_5556_,
        v_cmp_5557_,
        v_inst_5558_,
        v_inst_5559_,
        v_t_5560_,
    );
    crate::leanh::lean_dec(v_t_5560_);
    crate::leanh::lean_dec_ref(v_cmp_5557_);
    return v_res_5561_;
}
pub unsafe fn _init_l_Lean_RBMap_max_x21___redArg___closed__1() -> *mut crate::leanh::LeanObject {
    let mut v___x_5563_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5564_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5565_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5566_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5567_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5568_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5563_ = l_Lean_RBMap_min_x21___redArg___closed__2;
    v___x_5564_ = crate::leanh::lean_unsigned_to_nat(14);
    v___x_5565_ = crate::leanh::lean_unsigned_to_nat(389);
    v___x_5566_ = l_Lean_RBMap_max_x21___redArg___closed__0;
    v___x_5567_ = l_Lean_RBMap_min_x21___redArg___closed__0;
    v___x_5568_ = l_mkPanicMessageWithDecl(
        v___x_5567_,
        v___x_5566_,
        v___x_5565_,
        v___x_5564_,
        v___x_5563_,
    );
    return v___x_5568_;
}
pub unsafe fn l_Lean_RBMap_max_x21___redArg(
    mut v_inst_5569_: *mut crate::leanh::LeanObject,
    mut v_inst_5570_: *mut crate::leanh::LeanObject,
    mut v_t_5571_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5572_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5573_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5574_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5575_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_5576_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_5577_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_5578_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5580_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5581_: u8 = 0;
    let mut v___x_5583_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5584_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5585_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5572_ = l_Lean_RBNode_max___redArg(v_t_5571_);
                if crate::leanh::lean_obj_tag(v___x_5572_) == 0 {
                    v___x_5573_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_5573_, 0, v_inst_5569_);
                    crate::leanh::lean_ctor_set(v___x_5573_, 1, v_inst_5570_);
                    v___x_5574_ = crate::leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(l_Lean_RBMap_max_x21___redArg___closed__1),
                        core::ptr::addr_of_mut!(l_Lean_RBMap_max_x21___redArg___closed__1_once),
                        _init_l_Lean_RBMap_max_x21___redArg___closed__1,
                    );
                    v___x_5575_ = l_panic___redArg(v___x_5573_, v___x_5574_);
                    crate::leanh::lean_dec_ref_known(v___x_5573_, 2);
                    return v___x_5575_;
                } else {
                    crate::leanh::lean_dec(v_inst_5570_);
                    crate::leanh::lean_dec(v_inst_5569_);
                    v_val_5576_ = crate::leanh::lean_ctor_get(v___x_5572_, 0);
                    crate::leanh::lean_inc(v_val_5576_);
                    crate::leanh::lean_dec_ref_known(v___x_5572_, 1);
                    v_fst_5577_ = crate::leanh::lean_ctor_get(v_val_5576_, 0);
                    v_snd_5578_ = crate::leanh::lean_ctor_get(v_val_5576_, 1);
                    v_isSharedCheck_5585_ = (!crate::leanh::lean_is_exclusive(v_val_5576_)) as u8;
                    if v_isSharedCheck_5585_ == 0 {
                        v___x_5580_ = v_val_5576_;
                        v_isShared_5581_ = v_isSharedCheck_5585_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_snd_5578_);
                        crate::leanh::lean_inc(v_fst_5577_);
                        crate::leanh::lean_dec(v_val_5576_);
                        v___x_5580_ = crate::leanh::lean_box(0);
                        v_isShared_5581_ = v_isSharedCheck_5585_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_5581_ == 0 {
                    v___x_5583_ = v___x_5580_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_5584_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5584_, 0, v_fst_5577_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5584_, 1, v_snd_5578_);
                    v___x_5583_ = v_reuseFailAlloc_5584_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_5583_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_RBMap_max_x21___redArg___boxed(
    mut v_inst_5586_: *mut crate::leanh::LeanObject,
    mut v_inst_5587_: *mut crate::leanh::LeanObject,
    mut v_t_5588_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5589_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5589_ = l_Lean_RBMap_max_x21___redArg(v_inst_5586_, v_inst_5587_, v_t_5588_);
    crate::leanh::lean_dec(v_t_5588_);
    return v_res_5589_;
}
pub unsafe fn l_Lean_RBMap_max_x21(
    mut v_00_u03b1_5590_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_5591_: *mut crate::leanh::LeanObject,
    mut v_cmp_5592_: *mut crate::leanh::LeanObject,
    mut v_inst_5593_: *mut crate::leanh::LeanObject,
    mut v_inst_5594_: *mut crate::leanh::LeanObject,
    mut v_t_5595_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5596_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5597_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5598_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5599_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_5600_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_5601_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_5602_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5604_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5605_: u8 = 0;
    let mut v___x_5607_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5608_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5609_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5596_ = l_Lean_RBNode_max___redArg(v_t_5595_);
                if crate::leanh::lean_obj_tag(v___x_5596_) == 0 {
                    v___x_5597_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_5597_, 0, v_inst_5593_);
                    crate::leanh::lean_ctor_set(v___x_5597_, 1, v_inst_5594_);
                    v___x_5598_ = crate::leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(l_Lean_RBMap_max_x21___redArg___closed__1),
                        core::ptr::addr_of_mut!(l_Lean_RBMap_max_x21___redArg___closed__1_once),
                        _init_l_Lean_RBMap_max_x21___redArg___closed__1,
                    );
                    v___x_5599_ = l_panic___redArg(v___x_5597_, v___x_5598_);
                    crate::leanh::lean_dec_ref_known(v___x_5597_, 2);
                    return v___x_5599_;
                } else {
                    crate::leanh::lean_dec(v_inst_5594_);
                    crate::leanh::lean_dec(v_inst_5593_);
                    v_val_5600_ = crate::leanh::lean_ctor_get(v___x_5596_, 0);
                    crate::leanh::lean_inc(v_val_5600_);
                    crate::leanh::lean_dec_ref_known(v___x_5596_, 1);
                    v_fst_5601_ = crate::leanh::lean_ctor_get(v_val_5600_, 0);
                    v_snd_5602_ = crate::leanh::lean_ctor_get(v_val_5600_, 1);
                    v_isSharedCheck_5609_ = (!crate::leanh::lean_is_exclusive(v_val_5600_)) as u8;
                    if v_isSharedCheck_5609_ == 0 {
                        v___x_5604_ = v_val_5600_;
                        v_isShared_5605_ = v_isSharedCheck_5609_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_snd_5602_);
                        crate::leanh::lean_inc(v_fst_5601_);
                        crate::leanh::lean_dec(v_val_5600_);
                        v___x_5604_ = crate::leanh::lean_box(0);
                        v_isShared_5605_ = v_isSharedCheck_5609_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_5605_ == 0 {
                    v___x_5607_ = v___x_5604_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_5608_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5608_, 0, v_fst_5601_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5608_, 1, v_snd_5602_);
                    v___x_5607_ = v_reuseFailAlloc_5608_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_5607_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_RBMap_max_x21___boxed(
    mut v_00_u03b1_5610_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_5611_: *mut crate::leanh::LeanObject,
    mut v_cmp_5612_: *mut crate::leanh::LeanObject,
    mut v_inst_5613_: *mut crate::leanh::LeanObject,
    mut v_inst_5614_: *mut crate::leanh::LeanObject,
    mut v_t_5615_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5616_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5616_ = l_Lean_RBMap_max_x21(
        v_00_u03b1_5610_,
        v_00_u03b2_5611_,
        v_cmp_5612_,
        v_inst_5613_,
        v_inst_5614_,
        v_t_5615_,
    );
    crate::leanh::lean_dec(v_t_5615_);
    crate::leanh::lean_dec_ref(v_cmp_5612_);
    return v_res_5616_;
}
pub unsafe fn _init_l_Lean_RBMap_find_x21___redArg___closed__2() -> *mut crate::leanh::LeanObject {
    let mut v___x_5619_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5620_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5621_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5622_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5623_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5624_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5619_ = l_Lean_RBMap_find_x21___redArg___closed__1;
    v___x_5620_ = crate::leanh::lean_unsigned_to_nat(14);
    v___x_5621_ = crate::leanh::lean_unsigned_to_nat(395);
    v___x_5622_ = l_Lean_RBMap_find_x21___redArg___closed__0;
    v___x_5623_ = l_Lean_RBMap_min_x21___redArg___closed__0;
    v___x_5624_ = l_mkPanicMessageWithDecl(
        v___x_5623_,
        v___x_5622_,
        v___x_5621_,
        v___x_5620_,
        v___x_5619_,
    );
    return v___x_5624_;
}
pub unsafe fn l_Lean_RBMap_find_x21___redArg(
    mut v_cmp_5625_: *mut crate::leanh::LeanObject,
    mut v_inst_5626_: *mut crate::leanh::LeanObject,
    mut v_t_5627_: *mut crate::leanh::LeanObject,
    mut v_k_5628_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5629_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5629_ = l_Lean_RBNode_find___redArg(v_cmp_5625_, v_t_5627_, v_k_5628_);
    if crate::leanh::lean_obj_tag(v___x_5629_) == 0 {
        let mut v___x_5630_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5631_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_5630_ = crate::leanh::lean_obj_once(
            core::ptr::addr_of_mut!(l_Lean_RBMap_find_x21___redArg___closed__2),
            core::ptr::addr_of_mut!(l_Lean_RBMap_find_x21___redArg___closed__2_once),
            _init_l_Lean_RBMap_find_x21___redArg___closed__2,
        );
        v___x_5631_ = l_panic___redArg(v_inst_5626_, v___x_5630_);
        return v___x_5631_;
    } else {
        let mut v_val_5632_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_val_5632_ = crate::leanh::lean_ctor_get(v___x_5629_, 0);
        crate::leanh::lean_inc(v_val_5632_);
        crate::leanh::lean_dec_ref_known(v___x_5629_, 1);
        return v_val_5632_;
    }
}
pub unsafe fn l_Lean_RBMap_find_x21___redArg___boxed(
    mut v_cmp_5633_: *mut crate::leanh::LeanObject,
    mut v_inst_5634_: *mut crate::leanh::LeanObject,
    mut v_t_5635_: *mut crate::leanh::LeanObject,
    mut v_k_5636_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5637_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5637_ = l_Lean_RBMap_find_x21___redArg(v_cmp_5633_, v_inst_5634_, v_t_5635_, v_k_5636_);
    crate::leanh::lean_dec(v_inst_5634_);
    return v_res_5637_;
}
pub unsafe fn l_Lean_RBMap_find_x21(
    mut v_00_u03b1_5638_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_5639_: *mut crate::leanh::LeanObject,
    mut v_cmp_5640_: *mut crate::leanh::LeanObject,
    mut v_inst_5641_: *mut crate::leanh::LeanObject,
    mut v_t_5642_: *mut crate::leanh::LeanObject,
    mut v_k_5643_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5644_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5644_ = l_Lean_RBNode_find___redArg(v_cmp_5640_, v_t_5642_, v_k_5643_);
    if crate::leanh::lean_obj_tag(v___x_5644_) == 0 {
        let mut v___x_5645_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5646_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_5645_ = crate::leanh::lean_obj_once(
            core::ptr::addr_of_mut!(l_Lean_RBMap_find_x21___redArg___closed__2),
            core::ptr::addr_of_mut!(l_Lean_RBMap_find_x21___redArg___closed__2_once),
            _init_l_Lean_RBMap_find_x21___redArg___closed__2,
        );
        v___x_5646_ = l_panic___redArg(v_inst_5641_, v___x_5645_);
        return v___x_5646_;
    } else {
        let mut v_val_5647_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_val_5647_ = crate::leanh::lean_ctor_get(v___x_5644_, 0);
        crate::leanh::lean_inc(v_val_5647_);
        crate::leanh::lean_dec_ref_known(v___x_5644_, 1);
        return v_val_5647_;
    }
}
pub unsafe fn l_Lean_RBMap_find_x21___boxed(
    mut v_00_u03b1_5648_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_5649_: *mut crate::leanh::LeanObject,
    mut v_cmp_5650_: *mut crate::leanh::LeanObject,
    mut v_inst_5651_: *mut crate::leanh::LeanObject,
    mut v_t_5652_: *mut crate::leanh::LeanObject,
    mut v_k_5653_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5654_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5654_ = l_Lean_RBMap_find_x21(
        v_00_u03b1_5648_,
        v_00_u03b2_5649_,
        v_cmp_5650_,
        v_inst_5651_,
        v_t_5652_,
        v_k_5653_,
    );
    crate::leanh::lean_dec(v_inst_5651_);
    return v_res_5654_;
}
pub unsafe fn l_Lean_RBNode_ins___at___00Lean_RBNode_insert___at___00Lean_RBMap_mergeBy_spec__0_spec__0___redArg(
    mut v_cmp_5655_: *mut crate::leanh::LeanObject,
    mut v_x_5656_: *mut crate::leanh::LeanObject,
    mut v_x_5657_: *mut crate::leanh::LeanObject,
    mut v_x_5658_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5659_: u8 = 0;
    let mut v___x_5660_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_color_5661_: u8 = 0;
    let mut v_lchild_5662_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_key_5663_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_5664_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_rchild_5665_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5667_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5668_: u8 = 0;
    let mut v___x_5669_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5670_: u8 = 0;
    let mut v___x_5671_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5673_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5674_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5676_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5677_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5678_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5680_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5681_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5682_: u8 = 0;
    let mut v_lchild_5683_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_key_5684_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_5685_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_rchild_5686_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5688_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5689_: u8 = 0;
    let mut v___x_5690_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5691_: u8 = 0;
    let mut v___x_5692_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_color_5693_: u8 = 0;
    let mut v_lchild_5694_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_key_5695_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_5696_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_rchild_5697_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5699_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_kx_5700_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_vx_5701_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_b_5702_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ky_5703_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_vy_5704_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_c_5705_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_kz_5706_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_vz_5707_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_d_5708_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5710_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5711_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5712_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5713_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_color_5714_: u8 = 0;
    let mut v_lchild_5715_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_key_5716_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_5717_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_rchild_5718_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_color_5719_: u8 = 0;
    let mut v_lchild_5720_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_key_5721_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_5722_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_rchild_5723_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5725_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5726_: u8 = 0;
    let mut v___x_5728_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5729_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5730_: u8 = 0;
    let mut v_unused_5731_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_5732_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_5733_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_5734_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5736_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5737_: u8 = 0;
    let mut v___x_5739_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5740_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5741_: u8 = 0;
    let mut v_unused_5742_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_5743_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_5744_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_5745_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_color_5746_: u8 = 0;
    let mut v_lchild_5747_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_key_5748_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_5749_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_rchild_5750_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5752_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5753_: u8 = 0;
    let mut v___x_5755_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5756_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5757_: u8 = 0;
    let mut v_unused_5758_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_5759_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_5760_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_5761_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5762_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5763_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5765_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5766_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5768_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5769_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5770_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_color_5771_: u8 = 0;
    let mut v_lchild_5772_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_key_5773_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_5774_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_rchild_5775_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5777_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_kx_5778_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_vx_5779_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_b_5780_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ky_5781_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_vy_5782_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_c_5783_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_kz_5784_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_vz_5785_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_d_5786_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5788_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5789_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5790_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5791_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_color_5792_: u8 = 0;
    let mut v_lchild_5793_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_key_5794_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_5795_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_rchild_5796_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_color_5797_: u8 = 0;
    let mut v_lchild_5798_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_key_5799_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_5800_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_rchild_5801_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5803_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5804_: u8 = 0;
    let mut v___x_5806_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5807_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5808_: u8 = 0;
    let mut v_unused_5809_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_5810_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_5811_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_5812_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5814_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5815_: u8 = 0;
    let mut v___x_5817_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5818_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5819_: u8 = 0;
    let mut v_unused_5820_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_5821_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_5822_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_5823_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_color_5824_: u8 = 0;
    let mut v_lchild_5825_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_key_5826_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_5827_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_rchild_5828_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5830_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5831_: u8 = 0;
    let mut v___x_5833_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5834_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5835_: u8 = 0;
    let mut v_unused_5836_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_5837_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_5838_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_5839_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5840_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5841_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5843_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5844_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5845_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_5656_) == 0 {
                    crate::leanh::lean_dec_ref(v_cmp_5655_);
                    v___x_5659_ = 0;
                    v___x_5660_ = crate::leanh::lean_alloc_ctor(1, 4, (1) as u32);
                    crate::leanh::lean_ctor_set(v___x_5660_, 0, v_x_5656_);
                    crate::leanh::lean_ctor_set(v___x_5660_, 1, v_x_5657_);
                    crate::leanh::lean_ctor_set(v___x_5660_, 2, v_x_5658_);
                    crate::leanh::lean_ctor_set(v___x_5660_, 3, v_x_5656_);
                    crate::leanh::lean_ctor_set_uint8(
                        v___x_5660_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 4) as u32,
                        v___x_5659_,
                    );
                    return v___x_5660_;
                } else {
                    v_color_5661_ = crate::leanh::lean_ctor_get_uint8(
                        v_x_5656_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 4) as u32,
                    );
                    if v_color_5661_ == 0 {
                        v_lchild_5662_ = crate::leanh::lean_ctor_get(v_x_5656_, 0);
                        v_key_5663_ = crate::leanh::lean_ctor_get(v_x_5656_, 1);
                        v_val_5664_ = crate::leanh::lean_ctor_get(v_x_5656_, 2);
                        v_rchild_5665_ = crate::leanh::lean_ctor_get(v_x_5656_, 3);
                        v_isSharedCheck_5682_ = (!crate::leanh::lean_is_exclusive(v_x_5656_)) as u8;
                        if v_isSharedCheck_5682_ == 0 {
                            v___x_5667_ = v_x_5656_;
                            v_isShared_5668_ = v_isSharedCheck_5682_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_rchild_5665_);
                            crate::leanh::lean_inc(v_val_5664_);
                            crate::leanh::lean_inc(v_key_5663_);
                            crate::leanh::lean_inc(v_lchild_5662_);
                            crate::leanh::lean_dec(v_x_5656_);
                            v___x_5667_ = crate::leanh::lean_box(0);
                            v_isShared_5668_ = v_isSharedCheck_5682_;
                            state = 1;
                            continue;
                        }
                    } else {
                        v_lchild_5683_ = crate::leanh::lean_ctor_get(v_x_5656_, 0);
                        v_key_5684_ = crate::leanh::lean_ctor_get(v_x_5656_, 1);
                        v_val_5685_ = crate::leanh::lean_ctor_get(v_x_5656_, 2);
                        v_rchild_5686_ = crate::leanh::lean_ctor_get(v_x_5656_, 3);
                        v_isSharedCheck_5845_ = (!crate::leanh::lean_is_exclusive(v_x_5656_)) as u8;
                        if v_isSharedCheck_5845_ == 0 {
                            v___x_5688_ = v_x_5656_;
                            v_isShared_5689_ = v_isSharedCheck_5845_;
                            state = 5;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_rchild_5686_);
                            crate::leanh::lean_inc(v_val_5685_);
                            crate::leanh::lean_inc(v_key_5684_);
                            crate::leanh::lean_inc(v_lchild_5683_);
                            crate::leanh::lean_dec(v_x_5656_);
                            v___x_5688_ = crate::leanh::lean_box(0);
                            v_isShared_5689_ = v_isSharedCheck_5845_;
                            state = 5;
                            continue;
                        }
                    }
                }
            }
            1 => {
                crate::leanh::lean_inc_ref(v_cmp_5655_);
                crate::leanh::lean_inc(v_key_5663_);
                crate::leanh::lean_inc(v_x_5657_);
                v___x_5669_ = crate::leanh::lean_apply_2(v_cmp_5655_, v_x_5657_, v_key_5663_);
                v___x_5670_ = (crate::leanh::lean_unbox(v___x_5669_) as u8);
                match v___x_5670_ {
                    0 => {
                        v___x_5671_ = l_Lean_RBNode_ins___at___00Lean_RBNode_insert___at___00Lean_RBMap_mergeBy_spec__0_spec__0___redArg(v_cmp_5655_, v_lchild_5662_, v_x_5657_, v_x_5658_);
                        if v_isShared_5668_ == 0 {
                            crate::leanh::lean_ctor_set(v___x_5667_, 0, v___x_5671_);
                            v___x_5673_ = v___x_5667_;
                            state = 2;
                            continue;
                        } else {
                            v_reuseFailAlloc_5674_ =
                                crate::leanh::lean_alloc_ctor(1, 4, (1) as u32);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_5674_, 0, v___x_5671_);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_5674_, 1, v_key_5663_);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_5674_, 2, v_val_5664_);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_5674_, 3, v_rchild_5665_);
                            crate::leanh::lean_ctor_set_uint8(
                                v_reuseFailAlloc_5674_,
                                (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 4) as u32,
                                v_color_5661_,
                            );
                            v___x_5673_ = v_reuseFailAlloc_5674_;
                            state = 2;
                            continue;
                        }
                    }
                    1 => {
                        crate::leanh::lean_dec(v_val_5664_);
                        crate::leanh::lean_dec(v_key_5663_);
                        crate::leanh::lean_dec_ref(v_cmp_5655_);
                        if v_isShared_5668_ == 0 {
                            crate::leanh::lean_ctor_set(v___x_5667_, 2, v_x_5658_);
                            crate::leanh::lean_ctor_set(v___x_5667_, 1, v_x_5657_);
                            v___x_5676_ = v___x_5667_;
                            state = 3;
                            continue;
                        } else {
                            v_reuseFailAlloc_5677_ =
                                crate::leanh::lean_alloc_ctor(1, 4, (1) as u32);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_5677_, 0, v_lchild_5662_);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_5677_, 1, v_x_5657_);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_5677_, 2, v_x_5658_);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_5677_, 3, v_rchild_5665_);
                            crate::leanh::lean_ctor_set_uint8(
                                v_reuseFailAlloc_5677_,
                                (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 4) as u32,
                                v_color_5661_,
                            );
                            v___x_5676_ = v_reuseFailAlloc_5677_;
                            state = 3;
                            continue;
                        }
                    }
                    _ => {
                        v___x_5678_ = l_Lean_RBNode_ins___at___00Lean_RBNode_insert___at___00Lean_RBMap_mergeBy_spec__0_spec__0___redArg(v_cmp_5655_, v_rchild_5665_, v_x_5657_, v_x_5658_);
                        if v_isShared_5668_ == 0 {
                            crate::leanh::lean_ctor_set(v___x_5667_, 3, v___x_5678_);
                            v___x_5680_ = v___x_5667_;
                            state = 4;
                            continue;
                        } else {
                            v_reuseFailAlloc_5681_ =
                                crate::leanh::lean_alloc_ctor(1, 4, (1) as u32);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_5681_, 0, v_lchild_5662_);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_5681_, 1, v_key_5663_);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_5681_, 2, v_val_5664_);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_5681_, 3, v___x_5678_);
                            crate::leanh::lean_ctor_set_uint8(
                                v_reuseFailAlloc_5681_,
                                (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 4) as u32,
                                v_color_5661_,
                            );
                            v___x_5680_ = v_reuseFailAlloc_5681_;
                            state = 4;
                            continue;
                        }
                    }
                }
            }
            2 => {
                return v___x_5673_;
            }
            3 => {
                return v___x_5676_;
            }
            4 => {
                return v___x_5680_;
            }
            5 => {
                crate::leanh::lean_inc_ref(v_cmp_5655_);
                crate::leanh::lean_inc(v_key_5684_);
                crate::leanh::lean_inc(v_x_5657_);
                v___x_5690_ = crate::leanh::lean_apply_2(v_cmp_5655_, v_x_5657_, v_key_5684_);
                v___x_5691_ = (crate::leanh::lean_unbox(v___x_5690_) as u8);
                match v___x_5691_ {
                    0 => {
                        v___x_5692_ = l_Lean_RBNode_ins___at___00Lean_RBNode_insert___at___00Lean_RBMap_mergeBy_spec__0_spec__0___redArg(v_cmp_5655_, v_lchild_5683_, v_x_5657_, v_x_5658_);
                        if crate::leanh::lean_obj_tag(v___x_5692_) == 1 {
                            v_color_5693_ = crate::leanh::lean_ctor_get_uint8(
                                v___x_5692_,
                                (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 4) as u32,
                            );
                            v_lchild_5694_ = crate::leanh::lean_ctor_get(v___x_5692_, 0);
                            crate::leanh::lean_inc(v_lchild_5694_);
                            v_key_5695_ = crate::leanh::lean_ctor_get(v___x_5692_, 1);
                            crate::leanh::lean_inc(v_key_5695_);
                            v_val_5696_ = crate::leanh::lean_ctor_get(v___x_5692_, 2);
                            crate::leanh::lean_inc(v_val_5696_);
                            v_rchild_5697_ = crate::leanh::lean_ctor_get(v___x_5692_, 3);
                            crate::leanh::lean_inc(v_rchild_5697_);
                            if v_color_5693_ == 0 {
                                if crate::leanh::lean_obj_tag(v_lchild_5694_) == 1 {
                                    v_color_5714_ = crate::leanh::lean_ctor_get_uint8(
                                        v_lchild_5694_,
                                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 4)
                                            as u32,
                                    );
                                    if v_color_5714_ == 0 {
                                        crate::leanh::lean_dec_ref_known(v___x_5692_, 4);
                                        v_lchild_5715_ =
                                            crate::leanh::lean_ctor_get(v_lchild_5694_, 0);
                                        crate::leanh::lean_inc(v_lchild_5715_);
                                        v_key_5716_ =
                                            crate::leanh::lean_ctor_get(v_lchild_5694_, 1);
                                        crate::leanh::lean_inc(v_key_5716_);
                                        v_val_5717_ =
                                            crate::leanh::lean_ctor_get(v_lchild_5694_, 2);
                                        crate::leanh::lean_inc(v_val_5717_);
                                        v_rchild_5718_ =
                                            crate::leanh::lean_ctor_get(v_lchild_5694_, 3);
                                        crate::leanh::lean_inc(v_rchild_5718_);
                                        crate::leanh::lean_dec_ref_known(v_lchild_5694_, 4);
                                        v_a_5699_ = v_lchild_5715_;
                                        v_kx_5700_ = v_key_5716_;
                                        v_vx_5701_ = v_val_5717_;
                                        v_b_5702_ = v_rchild_5718_;
                                        v_ky_5703_ = v_key_5695_;
                                        v_vy_5704_ = v_val_5696_;
                                        v_c_5705_ = v_rchild_5697_;
                                        v_kz_5706_ = v_key_5684_;
                                        v_vz_5707_ = v_val_5685_;
                                        v_d_5708_ = v_rchild_5686_;
                                        state = 6;
                                        continue;
                                    } else {
                                        if crate::leanh::lean_obj_tag(v_rchild_5697_) == 1 {
                                            v_color_5719_ = crate::leanh::lean_ctor_get_uint8(
                                                v_rchild_5697_,
                                                (core::mem::size_of::<*mut crate::leanh::LeanObject>(
                                                ) * 4)
                                                    as u32,
                                            );
                                            if v_color_5719_ == 0 {
                                                crate::leanh::lean_dec_ref_known(v___x_5692_, 4);
                                                v_lchild_5720_ =
                                                    crate::leanh::lean_ctor_get(v_rchild_5697_, 0);
                                                crate::leanh::lean_inc(v_lchild_5720_);
                                                v_key_5721_ =
                                                    crate::leanh::lean_ctor_get(v_rchild_5697_, 1);
                                                crate::leanh::lean_inc(v_key_5721_);
                                                v_val_5722_ =
                                                    crate::leanh::lean_ctor_get(v_rchild_5697_, 2);
                                                crate::leanh::lean_inc(v_val_5722_);
                                                v_rchild_5723_ =
                                                    crate::leanh::lean_ctor_get(v_rchild_5697_, 3);
                                                crate::leanh::lean_inc(v_rchild_5723_);
                                                crate::leanh::lean_dec_ref_known(v_rchild_5697_, 4);
                                                v_a_5699_ = v_lchild_5694_;
                                                v_kx_5700_ = v_key_5695_;
                                                v_vx_5701_ = v_val_5696_;
                                                v_b_5702_ = v_lchild_5720_;
                                                v_ky_5703_ = v_key_5721_;
                                                v_vy_5704_ = v_val_5722_;
                                                v_c_5705_ = v_rchild_5723_;
                                                v_kz_5706_ = v_key_5684_;
                                                v_vz_5707_ = v_val_5685_;
                                                v_d_5708_ = v_rchild_5686_;
                                                state = 6;
                                                continue;
                                            } else {
                                                crate::leanh::lean_dec_ref_known(v_lchild_5694_, 4);
                                                crate::leanh::lean_dec(v_val_5696_);
                                                crate::leanh::lean_dec(v_key_5695_);
                                                crate::leanh::lean_del_object(v___x_5688_);
                                                v_isSharedCheck_5730_ =
                                                    (!crate::leanh::lean_is_exclusive(
                                                        v_rchild_5697_,
                                                    ))
                                                        as u8;
                                                if v_isSharedCheck_5730_ == 0 {
                                                    v_unused_5731_ = crate::leanh::lean_ctor_get(
                                                        v_rchild_5697_,
                                                        3,
                                                    );
                                                    crate::leanh::lean_dec(v_unused_5731_);
                                                    v_unused_5732_ = crate::leanh::lean_ctor_get(
                                                        v_rchild_5697_,
                                                        2,
                                                    );
                                                    crate::leanh::lean_dec(v_unused_5732_);
                                                    v_unused_5733_ = crate::leanh::lean_ctor_get(
                                                        v_rchild_5697_,
                                                        1,
                                                    );
                                                    crate::leanh::lean_dec(v_unused_5733_);
                                                    v_unused_5734_ = crate::leanh::lean_ctor_get(
                                                        v_rchild_5697_,
                                                        0,
                                                    );
                                                    crate::leanh::lean_dec(v_unused_5734_);
                                                    v___x_5725_ = v_rchild_5697_;
                                                    v_isShared_5726_ = v_isSharedCheck_5730_;
                                                    state = 8;
                                                    continue;
                                                } else {
                                                    crate::leanh::lean_dec(v_rchild_5697_);
                                                    v___x_5725_ = crate::leanh::lean_box(0);
                                                    v_isShared_5726_ = v_isSharedCheck_5730_;
                                                    state = 8;
                                                    continue;
                                                }
                                            }
                                        } else {
                                            crate::leanh::lean_dec(v_rchild_5697_);
                                            crate::leanh::lean_dec(v_val_5696_);
                                            crate::leanh::lean_dec(v_key_5695_);
                                            crate::leanh::lean_del_object(v___x_5688_);
                                            v_isSharedCheck_5741_ =
                                                (!crate::leanh::lean_is_exclusive(v_lchild_5694_))
                                                    as u8;
                                            if v_isSharedCheck_5741_ == 0 {
                                                v_unused_5742_ =
                                                    crate::leanh::lean_ctor_get(v_lchild_5694_, 3);
                                                crate::leanh::lean_dec(v_unused_5742_);
                                                v_unused_5743_ =
                                                    crate::leanh::lean_ctor_get(v_lchild_5694_, 2);
                                                crate::leanh::lean_dec(v_unused_5743_);
                                                v_unused_5744_ =
                                                    crate::leanh::lean_ctor_get(v_lchild_5694_, 1);
                                                crate::leanh::lean_dec(v_unused_5744_);
                                                v_unused_5745_ =
                                                    crate::leanh::lean_ctor_get(v_lchild_5694_, 0);
                                                crate::leanh::lean_dec(v_unused_5745_);
                                                v___x_5736_ = v_lchild_5694_;
                                                v_isShared_5737_ = v_isSharedCheck_5741_;
                                                state = 10;
                                                continue;
                                            } else {
                                                crate::leanh::lean_dec(v_lchild_5694_);
                                                v___x_5736_ = crate::leanh::lean_box(0);
                                                v_isShared_5737_ = v_isSharedCheck_5741_;
                                                state = 10;
                                                continue;
                                            }
                                        }
                                    }
                                } else {
                                    if crate::leanh::lean_obj_tag(v_rchild_5697_) == 1 {
                                        v_color_5746_ = crate::leanh::lean_ctor_get_uint8(
                                            v_rchild_5697_,
                                            (core::mem::size_of::<*mut crate::leanh::LeanObject>()
                                                * 4)
                                                as u32,
                                        );
                                        if v_color_5746_ == 0 {
                                            crate::leanh::lean_dec_ref_known(v___x_5692_, 4);
                                            v_lchild_5747_ =
                                                crate::leanh::lean_ctor_get(v_rchild_5697_, 0);
                                            crate::leanh::lean_inc(v_lchild_5747_);
                                            v_key_5748_ =
                                                crate::leanh::lean_ctor_get(v_rchild_5697_, 1);
                                            crate::leanh::lean_inc(v_key_5748_);
                                            v_val_5749_ =
                                                crate::leanh::lean_ctor_get(v_rchild_5697_, 2);
                                            crate::leanh::lean_inc(v_val_5749_);
                                            v_rchild_5750_ =
                                                crate::leanh::lean_ctor_get(v_rchild_5697_, 3);
                                            crate::leanh::lean_inc(v_rchild_5750_);
                                            crate::leanh::lean_dec_ref_known(v_rchild_5697_, 4);
                                            v_a_5699_ = v_lchild_5694_;
                                            v_kx_5700_ = v_key_5695_;
                                            v_vx_5701_ = v_val_5696_;
                                            v_b_5702_ = v_lchild_5747_;
                                            v_ky_5703_ = v_key_5748_;
                                            v_vy_5704_ = v_val_5749_;
                                            v_c_5705_ = v_rchild_5750_;
                                            v_kz_5706_ = v_key_5684_;
                                            v_vz_5707_ = v_val_5685_;
                                            v_d_5708_ = v_rchild_5686_;
                                            state = 6;
                                            continue;
                                        } else {
                                            crate::leanh::lean_dec(v_val_5696_);
                                            crate::leanh::lean_dec(v_key_5695_);
                                            crate::leanh::lean_dec(v_lchild_5694_);
                                            crate::leanh::lean_del_object(v___x_5688_);
                                            v_isSharedCheck_5757_ =
                                                (!crate::leanh::lean_is_exclusive(v_rchild_5697_))
                                                    as u8;
                                            if v_isSharedCheck_5757_ == 0 {
                                                v_unused_5758_ =
                                                    crate::leanh::lean_ctor_get(v_rchild_5697_, 3);
                                                crate::leanh::lean_dec(v_unused_5758_);
                                                v_unused_5759_ =
                                                    crate::leanh::lean_ctor_get(v_rchild_5697_, 2);
                                                crate::leanh::lean_dec(v_unused_5759_);
                                                v_unused_5760_ =
                                                    crate::leanh::lean_ctor_get(v_rchild_5697_, 1);
                                                crate::leanh::lean_dec(v_unused_5760_);
                                                v_unused_5761_ =
                                                    crate::leanh::lean_ctor_get(v_rchild_5697_, 0);
                                                crate::leanh::lean_dec(v_unused_5761_);
                                                v___x_5752_ = v_rchild_5697_;
                                                v_isShared_5753_ = v_isSharedCheck_5757_;
                                                state = 12;
                                                continue;
                                            } else {
                                                crate::leanh::lean_dec(v_rchild_5697_);
                                                v___x_5752_ = crate::leanh::lean_box(0);
                                                v_isShared_5753_ = v_isSharedCheck_5757_;
                                                state = 12;
                                                continue;
                                            }
                                        }
                                    } else {
                                        crate::leanh::lean_dec(v_rchild_5697_);
                                        crate::leanh::lean_dec(v_val_5696_);
                                        crate::leanh::lean_dec(v_key_5695_);
                                        crate::leanh::lean_dec(v_lchild_5694_);
                                        crate::leanh::lean_del_object(v___x_5688_);
                                        v___x_5762_ =
                                            crate::leanh::lean_alloc_ctor(1, 4, (1) as u32);
                                        crate::leanh::lean_ctor_set(v___x_5762_, 0, v___x_5692_);
                                        crate::leanh::lean_ctor_set(v___x_5762_, 1, v_key_5684_);
                                        crate::leanh::lean_ctor_set(v___x_5762_, 2, v_val_5685_);
                                        crate::leanh::lean_ctor_set(v___x_5762_, 3, v_rchild_5686_);
                                        crate::leanh::lean_ctor_set_uint8(
                                            v___x_5762_,
                                            (core::mem::size_of::<*mut crate::leanh::LeanObject>()
                                                * 4)
                                                as u32,
                                            v_color_5661_,
                                        );
                                        return v___x_5762_;
                                    }
                                }
                            } else {
                                crate::leanh::lean_dec(v_rchild_5697_);
                                crate::leanh::lean_dec(v_val_5696_);
                                crate::leanh::lean_dec(v_key_5695_);
                                crate::leanh::lean_dec(v_lchild_5694_);
                                crate::leanh::lean_del_object(v___x_5688_);
                                v___x_5763_ = crate::leanh::lean_alloc_ctor(1, 4, (1) as u32);
                                crate::leanh::lean_ctor_set(v___x_5763_, 0, v___x_5692_);
                                crate::leanh::lean_ctor_set(v___x_5763_, 1, v_key_5684_);
                                crate::leanh::lean_ctor_set(v___x_5763_, 2, v_val_5685_);
                                crate::leanh::lean_ctor_set(v___x_5763_, 3, v_rchild_5686_);
                                crate::leanh::lean_ctor_set_uint8(
                                    v___x_5763_,
                                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 4)
                                        as u32,
                                    v_color_5661_,
                                );
                                return v___x_5763_;
                            }
                        } else {
                            if v_isShared_5689_ == 0 {
                                crate::leanh::lean_ctor_set(v___x_5688_, 0, v___x_5692_);
                                v___x_5765_ = v___x_5688_;
                                state = 14;
                                continue;
                            } else {
                                v_reuseFailAlloc_5766_ =
                                    crate::leanh::lean_alloc_ctor(1, 4, (1) as u32);
                                crate::leanh::lean_ctor_set(v_reuseFailAlloc_5766_, 0, v___x_5692_);
                                crate::leanh::lean_ctor_set(v_reuseFailAlloc_5766_, 1, v_key_5684_);
                                crate::leanh::lean_ctor_set(v_reuseFailAlloc_5766_, 2, v_val_5685_);
                                crate::leanh::lean_ctor_set(
                                    v_reuseFailAlloc_5766_,
                                    3,
                                    v_rchild_5686_,
                                );
                                crate::leanh::lean_ctor_set_uint8(
                                    v_reuseFailAlloc_5766_,
                                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 4)
                                        as u32,
                                    v_color_5661_,
                                );
                                v___x_5765_ = v_reuseFailAlloc_5766_;
                                state = 14;
                                continue;
                            }
                        }
                    }
                    1 => {
                        crate::leanh::lean_dec(v_val_5685_);
                        crate::leanh::lean_dec(v_key_5684_);
                        crate::leanh::lean_dec_ref(v_cmp_5655_);
                        if v_isShared_5689_ == 0 {
                            crate::leanh::lean_ctor_set(v___x_5688_, 2, v_x_5658_);
                            crate::leanh::lean_ctor_set(v___x_5688_, 1, v_x_5657_);
                            v___x_5768_ = v___x_5688_;
                            state = 15;
                            continue;
                        } else {
                            v_reuseFailAlloc_5769_ =
                                crate::leanh::lean_alloc_ctor(1, 4, (1) as u32);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_5769_, 0, v_lchild_5683_);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_5769_, 1, v_x_5657_);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_5769_, 2, v_x_5658_);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_5769_, 3, v_rchild_5686_);
                            crate::leanh::lean_ctor_set_uint8(
                                v_reuseFailAlloc_5769_,
                                (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 4) as u32,
                                v_color_5661_,
                            );
                            v___x_5768_ = v_reuseFailAlloc_5769_;
                            state = 15;
                            continue;
                        }
                    }
                    _ => {
                        v___x_5770_ = l_Lean_RBNode_ins___at___00Lean_RBNode_insert___at___00Lean_RBMap_mergeBy_spec__0_spec__0___redArg(v_cmp_5655_, v_rchild_5686_, v_x_5657_, v_x_5658_);
                        if crate::leanh::lean_obj_tag(v___x_5770_) == 1 {
                            v_color_5771_ = crate::leanh::lean_ctor_get_uint8(
                                v___x_5770_,
                                (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 4) as u32,
                            );
                            v_lchild_5772_ = crate::leanh::lean_ctor_get(v___x_5770_, 0);
                            crate::leanh::lean_inc(v_lchild_5772_);
                            v_key_5773_ = crate::leanh::lean_ctor_get(v___x_5770_, 1);
                            crate::leanh::lean_inc(v_key_5773_);
                            v_val_5774_ = crate::leanh::lean_ctor_get(v___x_5770_, 2);
                            crate::leanh::lean_inc(v_val_5774_);
                            v_rchild_5775_ = crate::leanh::lean_ctor_get(v___x_5770_, 3);
                            crate::leanh::lean_inc(v_rchild_5775_);
                            if v_color_5771_ == 0 {
                                if crate::leanh::lean_obj_tag(v_lchild_5772_) == 1 {
                                    v_color_5792_ = crate::leanh::lean_ctor_get_uint8(
                                        v_lchild_5772_,
                                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 4)
                                            as u32,
                                    );
                                    if v_color_5792_ == 0 {
                                        crate::leanh::lean_dec_ref_known(v___x_5770_, 4);
                                        v_lchild_5793_ =
                                            crate::leanh::lean_ctor_get(v_lchild_5772_, 0);
                                        crate::leanh::lean_inc(v_lchild_5793_);
                                        v_key_5794_ =
                                            crate::leanh::lean_ctor_get(v_lchild_5772_, 1);
                                        crate::leanh::lean_inc(v_key_5794_);
                                        v_val_5795_ =
                                            crate::leanh::lean_ctor_get(v_lchild_5772_, 2);
                                        crate::leanh::lean_inc(v_val_5795_);
                                        v_rchild_5796_ =
                                            crate::leanh::lean_ctor_get(v_lchild_5772_, 3);
                                        crate::leanh::lean_inc(v_rchild_5796_);
                                        crate::leanh::lean_dec_ref_known(v_lchild_5772_, 4);
                                        v_a_5777_ = v_lchild_5683_;
                                        v_kx_5778_ = v_key_5684_;
                                        v_vx_5779_ = v_val_5685_;
                                        v_b_5780_ = v_lchild_5793_;
                                        v_ky_5781_ = v_key_5794_;
                                        v_vy_5782_ = v_val_5795_;
                                        v_c_5783_ = v_rchild_5796_;
                                        v_kz_5784_ = v_key_5773_;
                                        v_vz_5785_ = v_val_5774_;
                                        v_d_5786_ = v_rchild_5775_;
                                        state = 16;
                                        continue;
                                    } else {
                                        if crate::leanh::lean_obj_tag(v_rchild_5775_) == 1 {
                                            v_color_5797_ = crate::leanh::lean_ctor_get_uint8(
                                                v_rchild_5775_,
                                                (core::mem::size_of::<*mut crate::leanh::LeanObject>(
                                                ) * 4)
                                                    as u32,
                                            );
                                            if v_color_5797_ == 0 {
                                                crate::leanh::lean_dec_ref_known(v___x_5770_, 4);
                                                v_lchild_5798_ =
                                                    crate::leanh::lean_ctor_get(v_rchild_5775_, 0);
                                                crate::leanh::lean_inc(v_lchild_5798_);
                                                v_key_5799_ =
                                                    crate::leanh::lean_ctor_get(v_rchild_5775_, 1);
                                                crate::leanh::lean_inc(v_key_5799_);
                                                v_val_5800_ =
                                                    crate::leanh::lean_ctor_get(v_rchild_5775_, 2);
                                                crate::leanh::lean_inc(v_val_5800_);
                                                v_rchild_5801_ =
                                                    crate::leanh::lean_ctor_get(v_rchild_5775_, 3);
                                                crate::leanh::lean_inc(v_rchild_5801_);
                                                crate::leanh::lean_dec_ref_known(v_rchild_5775_, 4);
                                                v_a_5777_ = v_lchild_5683_;
                                                v_kx_5778_ = v_key_5684_;
                                                v_vx_5779_ = v_val_5685_;
                                                v_b_5780_ = v_lchild_5772_;
                                                v_ky_5781_ = v_key_5773_;
                                                v_vy_5782_ = v_val_5774_;
                                                v_c_5783_ = v_lchild_5798_;
                                                v_kz_5784_ = v_key_5799_;
                                                v_vz_5785_ = v_val_5800_;
                                                v_d_5786_ = v_rchild_5801_;
                                                state = 16;
                                                continue;
                                            } else {
                                                crate::leanh::lean_dec_ref_known(v_lchild_5772_, 4);
                                                crate::leanh::lean_dec(v_val_5774_);
                                                crate::leanh::lean_dec(v_key_5773_);
                                                crate::leanh::lean_del_object(v___x_5688_);
                                                v_isSharedCheck_5808_ =
                                                    (!crate::leanh::lean_is_exclusive(
                                                        v_rchild_5775_,
                                                    ))
                                                        as u8;
                                                if v_isSharedCheck_5808_ == 0 {
                                                    v_unused_5809_ = crate::leanh::lean_ctor_get(
                                                        v_rchild_5775_,
                                                        3,
                                                    );
                                                    crate::leanh::lean_dec(v_unused_5809_);
                                                    v_unused_5810_ = crate::leanh::lean_ctor_get(
                                                        v_rchild_5775_,
                                                        2,
                                                    );
                                                    crate::leanh::lean_dec(v_unused_5810_);
                                                    v_unused_5811_ = crate::leanh::lean_ctor_get(
                                                        v_rchild_5775_,
                                                        1,
                                                    );
                                                    crate::leanh::lean_dec(v_unused_5811_);
                                                    v_unused_5812_ = crate::leanh::lean_ctor_get(
                                                        v_rchild_5775_,
                                                        0,
                                                    );
                                                    crate::leanh::lean_dec(v_unused_5812_);
                                                    v___x_5803_ = v_rchild_5775_;
                                                    v_isShared_5804_ = v_isSharedCheck_5808_;
                                                    state = 18;
                                                    continue;
                                                } else {
                                                    crate::leanh::lean_dec(v_rchild_5775_);
                                                    v___x_5803_ = crate::leanh::lean_box(0);
                                                    v_isShared_5804_ = v_isSharedCheck_5808_;
                                                    state = 18;
                                                    continue;
                                                }
                                            }
                                        } else {
                                            crate::leanh::lean_dec(v_rchild_5775_);
                                            crate::leanh::lean_dec(v_val_5774_);
                                            crate::leanh::lean_dec(v_key_5773_);
                                            crate::leanh::lean_del_object(v___x_5688_);
                                            v_isSharedCheck_5819_ =
                                                (!crate::leanh::lean_is_exclusive(v_lchild_5772_))
                                                    as u8;
                                            if v_isSharedCheck_5819_ == 0 {
                                                v_unused_5820_ =
                                                    crate::leanh::lean_ctor_get(v_lchild_5772_, 3);
                                                crate::leanh::lean_dec(v_unused_5820_);
                                                v_unused_5821_ =
                                                    crate::leanh::lean_ctor_get(v_lchild_5772_, 2);
                                                crate::leanh::lean_dec(v_unused_5821_);
                                                v_unused_5822_ =
                                                    crate::leanh::lean_ctor_get(v_lchild_5772_, 1);
                                                crate::leanh::lean_dec(v_unused_5822_);
                                                v_unused_5823_ =
                                                    crate::leanh::lean_ctor_get(v_lchild_5772_, 0);
                                                crate::leanh::lean_dec(v_unused_5823_);
                                                v___x_5814_ = v_lchild_5772_;
                                                v_isShared_5815_ = v_isSharedCheck_5819_;
                                                state = 20;
                                                continue;
                                            } else {
                                                crate::leanh::lean_dec(v_lchild_5772_);
                                                v___x_5814_ = crate::leanh::lean_box(0);
                                                v_isShared_5815_ = v_isSharedCheck_5819_;
                                                state = 20;
                                                continue;
                                            }
                                        }
                                    }
                                } else {
                                    if crate::leanh::lean_obj_tag(v_rchild_5775_) == 1 {
                                        v_color_5824_ = crate::leanh::lean_ctor_get_uint8(
                                            v_rchild_5775_,
                                            (core::mem::size_of::<*mut crate::leanh::LeanObject>()
                                                * 4)
                                                as u32,
                                        );
                                        if v_color_5824_ == 0 {
                                            crate::leanh::lean_dec_ref_known(v___x_5770_, 4);
                                            v_lchild_5825_ =
                                                crate::leanh::lean_ctor_get(v_rchild_5775_, 0);
                                            crate::leanh::lean_inc(v_lchild_5825_);
                                            v_key_5826_ =
                                                crate::leanh::lean_ctor_get(v_rchild_5775_, 1);
                                            crate::leanh::lean_inc(v_key_5826_);
                                            v_val_5827_ =
                                                crate::leanh::lean_ctor_get(v_rchild_5775_, 2);
                                            crate::leanh::lean_inc(v_val_5827_);
                                            v_rchild_5828_ =
                                                crate::leanh::lean_ctor_get(v_rchild_5775_, 3);
                                            crate::leanh::lean_inc(v_rchild_5828_);
                                            crate::leanh::lean_dec_ref_known(v_rchild_5775_, 4);
                                            v_a_5777_ = v_lchild_5683_;
                                            v_kx_5778_ = v_key_5684_;
                                            v_vx_5779_ = v_val_5685_;
                                            v_b_5780_ = v_lchild_5772_;
                                            v_ky_5781_ = v_key_5773_;
                                            v_vy_5782_ = v_val_5774_;
                                            v_c_5783_ = v_lchild_5825_;
                                            v_kz_5784_ = v_key_5826_;
                                            v_vz_5785_ = v_val_5827_;
                                            v_d_5786_ = v_rchild_5828_;
                                            state = 16;
                                            continue;
                                        } else {
                                            crate::leanh::lean_dec(v_val_5774_);
                                            crate::leanh::lean_dec(v_key_5773_);
                                            crate::leanh::lean_dec(v_lchild_5772_);
                                            crate::leanh::lean_del_object(v___x_5688_);
                                            v_isSharedCheck_5835_ =
                                                (!crate::leanh::lean_is_exclusive(v_rchild_5775_))
                                                    as u8;
                                            if v_isSharedCheck_5835_ == 0 {
                                                v_unused_5836_ =
                                                    crate::leanh::lean_ctor_get(v_rchild_5775_, 3);
                                                crate::leanh::lean_dec(v_unused_5836_);
                                                v_unused_5837_ =
                                                    crate::leanh::lean_ctor_get(v_rchild_5775_, 2);
                                                crate::leanh::lean_dec(v_unused_5837_);
                                                v_unused_5838_ =
                                                    crate::leanh::lean_ctor_get(v_rchild_5775_, 1);
                                                crate::leanh::lean_dec(v_unused_5838_);
                                                v_unused_5839_ =
                                                    crate::leanh::lean_ctor_get(v_rchild_5775_, 0);
                                                crate::leanh::lean_dec(v_unused_5839_);
                                                v___x_5830_ = v_rchild_5775_;
                                                v_isShared_5831_ = v_isSharedCheck_5835_;
                                                state = 22;
                                                continue;
                                            } else {
                                                crate::leanh::lean_dec(v_rchild_5775_);
                                                v___x_5830_ = crate::leanh::lean_box(0);
                                                v_isShared_5831_ = v_isSharedCheck_5835_;
                                                state = 22;
                                                continue;
                                            }
                                        }
                                    } else {
                                        crate::leanh::lean_dec(v_rchild_5775_);
                                        crate::leanh::lean_dec(v_val_5774_);
                                        crate::leanh::lean_dec(v_key_5773_);
                                        crate::leanh::lean_dec(v_lchild_5772_);
                                        crate::leanh::lean_del_object(v___x_5688_);
                                        v___x_5840_ =
                                            crate::leanh::lean_alloc_ctor(1, 4, (1) as u32);
                                        crate::leanh::lean_ctor_set(v___x_5840_, 0, v_lchild_5683_);
                                        crate::leanh::lean_ctor_set(v___x_5840_, 1, v_key_5684_);
                                        crate::leanh::lean_ctor_set(v___x_5840_, 2, v_val_5685_);
                                        crate::leanh::lean_ctor_set(v___x_5840_, 3, v___x_5770_);
                                        crate::leanh::lean_ctor_set_uint8(
                                            v___x_5840_,
                                            (core::mem::size_of::<*mut crate::leanh::LeanObject>()
                                                * 4)
                                                as u32,
                                            v_color_5661_,
                                        );
                                        return v___x_5840_;
                                    }
                                }
                            } else {
                                crate::leanh::lean_dec(v_rchild_5775_);
                                crate::leanh::lean_dec(v_val_5774_);
                                crate::leanh::lean_dec(v_key_5773_);
                                crate::leanh::lean_dec(v_lchild_5772_);
                                crate::leanh::lean_del_object(v___x_5688_);
                                v___x_5841_ = crate::leanh::lean_alloc_ctor(1, 4, (1) as u32);
                                crate::leanh::lean_ctor_set(v___x_5841_, 0, v_lchild_5683_);
                                crate::leanh::lean_ctor_set(v___x_5841_, 1, v_key_5684_);
                                crate::leanh::lean_ctor_set(v___x_5841_, 2, v_val_5685_);
                                crate::leanh::lean_ctor_set(v___x_5841_, 3, v___x_5770_);
                                crate::leanh::lean_ctor_set_uint8(
                                    v___x_5841_,
                                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 4)
                                        as u32,
                                    v_color_5661_,
                                );
                                return v___x_5841_;
                            }
                        } else {
                            if v_isShared_5689_ == 0 {
                                crate::leanh::lean_ctor_set(v___x_5688_, 3, v___x_5770_);
                                v___x_5843_ = v___x_5688_;
                                state = 24;
                                continue;
                            } else {
                                v_reuseFailAlloc_5844_ =
                                    crate::leanh::lean_alloc_ctor(1, 4, (1) as u32);
                                crate::leanh::lean_ctor_set(
                                    v_reuseFailAlloc_5844_,
                                    0,
                                    v_lchild_5683_,
                                );
                                crate::leanh::lean_ctor_set(v_reuseFailAlloc_5844_, 1, v_key_5684_);
                                crate::leanh::lean_ctor_set(v_reuseFailAlloc_5844_, 2, v_val_5685_);
                                crate::leanh::lean_ctor_set(v_reuseFailAlloc_5844_, 3, v___x_5770_);
                                crate::leanh::lean_ctor_set_uint8(
                                    v_reuseFailAlloc_5844_,
                                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 4)
                                        as u32,
                                    v_color_5661_,
                                );
                                v___x_5843_ = v_reuseFailAlloc_5844_;
                                state = 24;
                                continue;
                            }
                        }
                    }
                }
            }
            6 => {
                if v_isShared_5689_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_5688_, 3, v_b_5702_);
                    crate::leanh::lean_ctor_set(v___x_5688_, 2, v_vx_5701_);
                    crate::leanh::lean_ctor_set(v___x_5688_, 1, v_kx_5700_);
                    crate::leanh::lean_ctor_set(v___x_5688_, 0, v_a_5699_);
                    v___x_5710_ = v___x_5688_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_5713_ = crate::leanh::lean_alloc_ctor(1, 4, (1) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5713_, 0, v_a_5699_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5713_, 1, v_kx_5700_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5713_, 2, v_vx_5701_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5713_, 3, v_b_5702_);
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_5713_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 4) as u32,
                        v_color_5661_,
                    );
                    v___x_5710_ = v_reuseFailAlloc_5713_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                v___x_5711_ = crate::leanh::lean_alloc_ctor(1, 4, (1) as u32);
                crate::leanh::lean_ctor_set(v___x_5711_, 0, v_c_5705_);
                crate::leanh::lean_ctor_set(v___x_5711_, 1, v_kz_5706_);
                crate::leanh::lean_ctor_set(v___x_5711_, 2, v_vz_5707_);
                crate::leanh::lean_ctor_set(v___x_5711_, 3, v_d_5708_);
                crate::leanh::lean_ctor_set_uint8(
                    v___x_5711_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 4) as u32,
                    v_color_5661_,
                );
                v___x_5712_ = crate::leanh::lean_alloc_ctor(1, 4, (1) as u32);
                crate::leanh::lean_ctor_set(v___x_5712_, 0, v___x_5710_);
                crate::leanh::lean_ctor_set(v___x_5712_, 1, v_ky_5703_);
                crate::leanh::lean_ctor_set(v___x_5712_, 2, v_vy_5704_);
                crate::leanh::lean_ctor_set(v___x_5712_, 3, v___x_5711_);
                crate::leanh::lean_ctor_set_uint8(
                    v___x_5712_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 4) as u32,
                    v_color_5693_,
                );
                return v___x_5712_;
            }
            8 => {
                if v_isShared_5726_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_5725_, 3, v_rchild_5686_);
                    crate::leanh::lean_ctor_set(v___x_5725_, 2, v_val_5685_);
                    crate::leanh::lean_ctor_set(v___x_5725_, 1, v_key_5684_);
                    crate::leanh::lean_ctor_set(v___x_5725_, 0, v___x_5692_);
                    v___x_5728_ = v___x_5725_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_5729_ = crate::leanh::lean_alloc_ctor(1, 4, (1) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5729_, 0, v___x_5692_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5729_, 1, v_key_5684_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5729_, 2, v_val_5685_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5729_, 3, v_rchild_5686_);
                    v___x_5728_ = v_reuseFailAlloc_5729_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                crate::leanh::lean_ctor_set_uint8(
                    v___x_5728_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 4) as u32,
                    v_color_5661_,
                );
                return v___x_5728_;
            }
            10 => {
                if v_isShared_5737_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_5736_, 3, v_rchild_5686_);
                    crate::leanh::lean_ctor_set(v___x_5736_, 2, v_val_5685_);
                    crate::leanh::lean_ctor_set(v___x_5736_, 1, v_key_5684_);
                    crate::leanh::lean_ctor_set(v___x_5736_, 0, v___x_5692_);
                    v___x_5739_ = v___x_5736_;
                    state = 11;
                    continue;
                } else {
                    v_reuseFailAlloc_5740_ = crate::leanh::lean_alloc_ctor(1, 4, (1) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5740_, 0, v___x_5692_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5740_, 1, v_key_5684_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5740_, 2, v_val_5685_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5740_, 3, v_rchild_5686_);
                    v___x_5739_ = v_reuseFailAlloc_5740_;
                    state = 11;
                    continue;
                }
            }
            11 => {
                crate::leanh::lean_ctor_set_uint8(
                    v___x_5739_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 4) as u32,
                    v_color_5661_,
                );
                return v___x_5739_;
            }
            12 => {
                if v_isShared_5753_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_5752_, 3, v_rchild_5686_);
                    crate::leanh::lean_ctor_set(v___x_5752_, 2, v_val_5685_);
                    crate::leanh::lean_ctor_set(v___x_5752_, 1, v_key_5684_);
                    crate::leanh::lean_ctor_set(v___x_5752_, 0, v___x_5692_);
                    v___x_5755_ = v___x_5752_;
                    state = 13;
                    continue;
                } else {
                    v_reuseFailAlloc_5756_ = crate::leanh::lean_alloc_ctor(1, 4, (1) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5756_, 0, v___x_5692_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5756_, 1, v_key_5684_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5756_, 2, v_val_5685_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5756_, 3, v_rchild_5686_);
                    v___x_5755_ = v_reuseFailAlloc_5756_;
                    state = 13;
                    continue;
                }
            }
            13 => {
                crate::leanh::lean_ctor_set_uint8(
                    v___x_5755_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 4) as u32,
                    v_color_5661_,
                );
                return v___x_5755_;
            }
            14 => {
                return v___x_5765_;
            }
            15 => {
                return v___x_5768_;
            }
            16 => {
                if v_isShared_5689_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_5688_, 3, v_b_5780_);
                    crate::leanh::lean_ctor_set(v___x_5688_, 2, v_vx_5779_);
                    crate::leanh::lean_ctor_set(v___x_5688_, 1, v_kx_5778_);
                    crate::leanh::lean_ctor_set(v___x_5688_, 0, v_a_5777_);
                    v___x_5788_ = v___x_5688_;
                    state = 17;
                    continue;
                } else {
                    v_reuseFailAlloc_5791_ = crate::leanh::lean_alloc_ctor(1, 4, (1) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5791_, 0, v_a_5777_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5791_, 1, v_kx_5778_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5791_, 2, v_vx_5779_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5791_, 3, v_b_5780_);
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_5791_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 4) as u32,
                        v_color_5661_,
                    );
                    v___x_5788_ = v_reuseFailAlloc_5791_;
                    state = 17;
                    continue;
                }
            }
            17 => {
                v___x_5789_ = crate::leanh::lean_alloc_ctor(1, 4, (1) as u32);
                crate::leanh::lean_ctor_set(v___x_5789_, 0, v_c_5783_);
                crate::leanh::lean_ctor_set(v___x_5789_, 1, v_kz_5784_);
                crate::leanh::lean_ctor_set(v___x_5789_, 2, v_vz_5785_);
                crate::leanh::lean_ctor_set(v___x_5789_, 3, v_d_5786_);
                crate::leanh::lean_ctor_set_uint8(
                    v___x_5789_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 4) as u32,
                    v_color_5661_,
                );
                v___x_5790_ = crate::leanh::lean_alloc_ctor(1, 4, (1) as u32);
                crate::leanh::lean_ctor_set(v___x_5790_, 0, v___x_5788_);
                crate::leanh::lean_ctor_set(v___x_5790_, 1, v_ky_5781_);
                crate::leanh::lean_ctor_set(v___x_5790_, 2, v_vy_5782_);
                crate::leanh::lean_ctor_set(v___x_5790_, 3, v___x_5789_);
                crate::leanh::lean_ctor_set_uint8(
                    v___x_5790_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 4) as u32,
                    v_color_5771_,
                );
                return v___x_5790_;
            }
            18 => {
                if v_isShared_5804_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_5803_, 3, v___x_5770_);
                    crate::leanh::lean_ctor_set(v___x_5803_, 2, v_val_5685_);
                    crate::leanh::lean_ctor_set(v___x_5803_, 1, v_key_5684_);
                    crate::leanh::lean_ctor_set(v___x_5803_, 0, v_lchild_5683_);
                    v___x_5806_ = v___x_5803_;
                    state = 19;
                    continue;
                } else {
                    v_reuseFailAlloc_5807_ = crate::leanh::lean_alloc_ctor(1, 4, (1) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5807_, 0, v_lchild_5683_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5807_, 1, v_key_5684_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5807_, 2, v_val_5685_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5807_, 3, v___x_5770_);
                    v___x_5806_ = v_reuseFailAlloc_5807_;
                    state = 19;
                    continue;
                }
            }
            19 => {
                crate::leanh::lean_ctor_set_uint8(
                    v___x_5806_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 4) as u32,
                    v_color_5661_,
                );
                return v___x_5806_;
            }
            20 => {
                if v_isShared_5815_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_5814_, 3, v___x_5770_);
                    crate::leanh::lean_ctor_set(v___x_5814_, 2, v_val_5685_);
                    crate::leanh::lean_ctor_set(v___x_5814_, 1, v_key_5684_);
                    crate::leanh::lean_ctor_set(v___x_5814_, 0, v_lchild_5683_);
                    v___x_5817_ = v___x_5814_;
                    state = 21;
                    continue;
                } else {
                    v_reuseFailAlloc_5818_ = crate::leanh::lean_alloc_ctor(1, 4, (1) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5818_, 0, v_lchild_5683_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5818_, 1, v_key_5684_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5818_, 2, v_val_5685_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5818_, 3, v___x_5770_);
                    v___x_5817_ = v_reuseFailAlloc_5818_;
                    state = 21;
                    continue;
                }
            }
            21 => {
                crate::leanh::lean_ctor_set_uint8(
                    v___x_5817_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 4) as u32,
                    v_color_5661_,
                );
                return v___x_5817_;
            }
            22 => {
                if v_isShared_5831_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_5830_, 3, v___x_5770_);
                    crate::leanh::lean_ctor_set(v___x_5830_, 2, v_val_5685_);
                    crate::leanh::lean_ctor_set(v___x_5830_, 1, v_key_5684_);
                    crate::leanh::lean_ctor_set(v___x_5830_, 0, v_lchild_5683_);
                    v___x_5833_ = v___x_5830_;
                    state = 23;
                    continue;
                } else {
                    v_reuseFailAlloc_5834_ = crate::leanh::lean_alloc_ctor(1, 4, (1) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5834_, 0, v_lchild_5683_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5834_, 1, v_key_5684_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5834_, 2, v_val_5685_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5834_, 3, v___x_5770_);
                    v___x_5833_ = v_reuseFailAlloc_5834_;
                    state = 23;
                    continue;
                }
            }
            23 => {
                crate::leanh::lean_ctor_set_uint8(
                    v___x_5833_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 4) as u32,
                    v_color_5661_,
                );
                return v___x_5833_;
            }
            24 => {
                return v___x_5843_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_RBNode_insert___at___00Lean_RBMap_mergeBy_spec__0___redArg(
    mut v_cmp_5846_: *mut crate::leanh::LeanObject,
    mut v_t_5847_: *mut crate::leanh::LeanObject,
    mut v_k_5848_: *mut crate::leanh::LeanObject,
    mut v_v_5849_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5850_: u8 = 0;
    v___x_5850_ = l_Lean_RBNode_isRed___redArg(v_t_5847_);
    if v___x_5850_ == 0 {
        let mut v___x_5851_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_5851_ = l_Lean_RBNode_ins___at___00Lean_RBNode_insert___at___00Lean_RBMap_mergeBy_spec__0_spec__0___redArg(v_cmp_5846_, v_t_5847_, v_k_5848_, v_v_5849_);
        return v___x_5851_;
    } else {
        let mut v___x_5852_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5853_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_5852_ = l_Lean_RBNode_ins___at___00Lean_RBNode_insert___at___00Lean_RBMap_mergeBy_spec__0_spec__0___redArg(v_cmp_5846_, v_t_5847_, v_k_5848_, v_v_5849_);
        v___x_5853_ = l_Lean_RBNode_setBlack___redArg(v___x_5852_);
        return v___x_5853_;
    }
}
pub unsafe fn l_Lean_RBNode_find___at___00Lean_RBMap_mergeBy_spec__1___redArg(
    mut v_cmp_5854_: *mut crate::leanh::LeanObject,
    mut v_x_5855_: *mut crate::leanh::LeanObject,
    mut v_x_5856_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5857_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_lchild_5858_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_key_5859_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_5860_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_rchild_5861_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5862_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5863_: u8 = 0;
    let mut v___x_5865_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_5855_) == 0 {
                    crate::leanh::lean_dec(v_x_5856_);
                    crate::leanh::lean_dec_ref(v_cmp_5854_);
                    v___x_5857_ = crate::leanh::lean_box(0);
                    return v___x_5857_;
                } else {
                    v_lchild_5858_ = crate::leanh::lean_ctor_get(v_x_5855_, 0);
                    crate::leanh::lean_inc(v_lchild_5858_);
                    v_key_5859_ = crate::leanh::lean_ctor_get(v_x_5855_, 1);
                    crate::leanh::lean_inc(v_key_5859_);
                    v_val_5860_ = crate::leanh::lean_ctor_get(v_x_5855_, 2);
                    crate::leanh::lean_inc(v_val_5860_);
                    v_rchild_5861_ = crate::leanh::lean_ctor_get(v_x_5855_, 3);
                    crate::leanh::lean_inc(v_rchild_5861_);
                    crate::leanh::lean_dec_ref_known(v_x_5855_, 4);
                    crate::leanh::lean_inc_ref(v_cmp_5854_);
                    crate::leanh::lean_inc(v_x_5856_);
                    v___x_5862_ = crate::leanh::lean_apply_2(v_cmp_5854_, v_x_5856_, v_key_5859_);
                    v___x_5863_ = (crate::leanh::lean_unbox(v___x_5862_) as u8);
                    match v___x_5863_ {
                        0 => {
                            crate::leanh::lean_dec(v_rchild_5861_);
                            crate::leanh::lean_dec(v_val_5860_);
                            v_x_5855_ = v_lchild_5858_;
                            state = 0;
                            continue;
                        }
                        1 => {
                            crate::leanh::lean_dec(v_rchild_5861_);
                            crate::leanh::lean_dec(v_lchild_5858_);
                            crate::leanh::lean_dec(v_x_5856_);
                            crate::leanh::lean_dec_ref(v_cmp_5854_);
                            v___x_5865_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                            crate::leanh::lean_ctor_set(v___x_5865_, 0, v_val_5860_);
                            return v___x_5865_;
                        }
                        _ => {
                            crate::leanh::lean_dec(v_val_5860_);
                            crate::leanh::lean_dec(v_lchild_5858_);
                            v_x_5855_ = v_rchild_5861_;
                            state = 0;
                            continue;
                        }
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_RBNode_fold___at___00Lean_RBMap_mergeBy_spec__2___redArg(
    mut v_cmp_5867_: *mut crate::leanh::LeanObject,
    mut v_mergeFn_5868_: *mut crate::leanh::LeanObject,
    mut v_x_5869_: *mut crate::leanh::LeanObject,
    mut v_x_5870_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_lchild_5871_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_key_5872_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_5873_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_rchild_5874_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_5875_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5877_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5878_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5880_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_5881_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5882_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_5870_) == 0 {
                    crate::leanh::lean_dec(v_mergeFn_5868_);
                    crate::leanh::lean_dec_ref(v_cmp_5867_);
                    return v_x_5869_;
                } else {
                    v_lchild_5871_ = crate::leanh::lean_ctor_get(v_x_5870_, 0);
                    crate::leanh::lean_inc(v_lchild_5871_);
                    v_key_5872_ = crate::leanh::lean_ctor_get(v_x_5870_, 1);
                    crate::leanh::lean_inc_n(v_key_5872_, 2);
                    v_val_5873_ = crate::leanh::lean_ctor_get(v_x_5870_, 2);
                    crate::leanh::lean_inc(v_val_5873_);
                    v_rchild_5874_ = crate::leanh::lean_ctor_get(v_x_5870_, 3);
                    crate::leanh::lean_inc(v_rchild_5874_);
                    crate::leanh::lean_dec_ref_known(v_x_5870_, 4);
                    crate::leanh::lean_inc(v_mergeFn_5868_);
                    crate::leanh::lean_inc_ref_n(v_cmp_5867_, 2);
                    v_val_5875_ = l_Lean_RBNode_fold___at___00Lean_RBMap_mergeBy_spec__2___redArg(
                        v_cmp_5867_,
                        v_mergeFn_5868_,
                        v_x_5869_,
                        v_lchild_5871_,
                    );
                    crate::leanh::lean_inc(v_val_5875_);
                    v___x_5880_ = l_Lean_RBNode_find___at___00Lean_RBMap_mergeBy_spec__1___redArg(
                        v_cmp_5867_,
                        v_val_5875_,
                        v_key_5872_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_5880_) == 0 {
                        v___y_5877_ = v_val_5873_;
                        state = 1;
                        continue;
                    } else {
                        v_val_5881_ = crate::leanh::lean_ctor_get(v___x_5880_, 0);
                        crate::leanh::lean_inc(v_val_5881_);
                        crate::leanh::lean_dec_ref_known(v___x_5880_, 1);
                        crate::leanh::lean_inc(v_mergeFn_5868_);
                        crate::leanh::lean_inc(v_key_5872_);
                        v___x_5882_ = crate::leanh::lean_apply_3(
                            v_mergeFn_5868_,
                            v_key_5872_,
                            v_val_5881_,
                            v_val_5873_,
                        );
                        v___y_5877_ = v___x_5882_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                crate::leanh::lean_inc_ref(v_cmp_5867_);
                v___x_5878_ = l_Lean_RBNode_insert___at___00Lean_RBMap_mergeBy_spec__0___redArg(
                    v_cmp_5867_,
                    v_val_5875_,
                    v_key_5872_,
                    v___y_5877_,
                );
                v_x_5869_ = v___x_5878_;
                v_x_5870_ = v_rchild_5874_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_RBMap_mergeBy___redArg(
    mut v_cmp_5883_: *mut crate::leanh::LeanObject,
    mut v_mergeFn_5884_: *mut crate::leanh::LeanObject,
    mut v_t_u2081_5885_: *mut crate::leanh::LeanObject,
    mut v_t_u2082_5886_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5887_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5887_ = l_Lean_RBNode_fold___at___00Lean_RBMap_mergeBy_spec__2___redArg(
        v_cmp_5883_,
        v_mergeFn_5884_,
        v_t_u2081_5885_,
        v_t_u2082_5886_,
    );
    return v___x_5887_;
}
pub unsafe fn l_Lean_RBMap_mergeBy(
    mut v_00_u03b1_5888_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_5889_: *mut crate::leanh::LeanObject,
    mut v_cmp_5890_: *mut crate::leanh::LeanObject,
    mut v_mergeFn_5891_: *mut crate::leanh::LeanObject,
    mut v_t_u2081_5892_: *mut crate::leanh::LeanObject,
    mut v_t_u2082_5893_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5894_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5894_ = l_Lean_RBNode_fold___at___00Lean_RBMap_mergeBy_spec__2___redArg(
        v_cmp_5890_,
        v_mergeFn_5891_,
        v_t_u2081_5892_,
        v_t_u2082_5893_,
    );
    return v___x_5894_;
}
pub unsafe fn l_Lean_RBNode_insert___at___00Lean_RBMap_mergeBy_spec__0(
    mut v_00_u03b1_5895_: *mut crate::leanh::LeanObject,
    mut v_cmp_5896_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_5897_: *mut crate::leanh::LeanObject,
    mut v_t_5898_: *mut crate::leanh::LeanObject,
    mut v_k_5899_: *mut crate::leanh::LeanObject,
    mut v_v_5900_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5901_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5901_ = l_Lean_RBNode_insert___at___00Lean_RBMap_mergeBy_spec__0___redArg(
        v_cmp_5896_,
        v_t_5898_,
        v_k_5899_,
        v_v_5900_,
    );
    return v___x_5901_;
}
pub unsafe fn l_Lean_RBNode_find___at___00Lean_RBMap_mergeBy_spec__1(
    mut v_00_u03b1_5902_: *mut crate::leanh::LeanObject,
    mut v_cmp_5903_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_5904_: *mut crate::leanh::LeanObject,
    mut v_x_5905_: *mut crate::leanh::LeanObject,
    mut v_x_5906_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5907_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5907_ = l_Lean_RBNode_find___at___00Lean_RBMap_mergeBy_spec__1___redArg(
        v_cmp_5903_,
        v_x_5905_,
        v_x_5906_,
    );
    return v___x_5907_;
}
pub unsafe fn l_Lean_RBNode_fold___at___00Lean_RBMap_mergeBy_spec__2(
    mut v_00_u03b1_5908_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_5909_: *mut crate::leanh::LeanObject,
    mut v_cmp_5910_: *mut crate::leanh::LeanObject,
    mut v_mergeFn_5911_: *mut crate::leanh::LeanObject,
    mut v_x_5912_: *mut crate::leanh::LeanObject,
    mut v_x_5913_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5914_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5914_ = l_Lean_RBNode_fold___at___00Lean_RBMap_mergeBy_spec__2___redArg(
        v_cmp_5910_,
        v_mergeFn_5911_,
        v_x_5912_,
        v_x_5913_,
    );
    return v___x_5914_;
}
pub unsafe fn l_Lean_RBNode_ins___at___00Lean_RBNode_insert___at___00Lean_RBMap_mergeBy_spec__0_spec__0(
    mut v_00_u03b1_5915_: *mut crate::leanh::LeanObject,
    mut v_cmp_5916_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_5917_: *mut crate::leanh::LeanObject,
    mut v_x_5918_: *mut crate::leanh::LeanObject,
    mut v_x_5919_: *mut crate::leanh::LeanObject,
    mut v_x_5920_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5921_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5921_ = l_Lean_RBNode_ins___at___00Lean_RBNode_insert___at___00Lean_RBMap_mergeBy_spec__0_spec__0___redArg(v_cmp_5916_, v_x_5918_, v_x_5919_, v_x_5920_);
    return v___x_5921_;
}
pub unsafe fn l_Lean_RBNode_fold___at___00Lean_RBMap_intersectBy_spec__0___redArg(
    mut v_t_u2082_5922_: *mut crate::leanh::LeanObject,
    mut v_cmp_5923_: *mut crate::leanh::LeanObject,
    mut v_mergeFn_5924_: *mut crate::leanh::LeanObject,
    mut v_x_5925_: *mut crate::leanh::LeanObject,
    mut v_x_5926_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_lchild_5927_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_key_5928_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_5929_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_rchild_5930_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_5931_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5932_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_5934_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5935_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5936_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_5926_) == 0 {
                    crate::leanh::lean_dec(v_mergeFn_5924_);
                    crate::leanh::lean_dec_ref(v_cmp_5923_);
                    crate::leanh::lean_dec(v_t_u2082_5922_);
                    return v_x_5925_;
                } else {
                    v_lchild_5927_ = crate::leanh::lean_ctor_get(v_x_5926_, 0);
                    crate::leanh::lean_inc(v_lchild_5927_);
                    v_key_5928_ = crate::leanh::lean_ctor_get(v_x_5926_, 1);
                    crate::leanh::lean_inc_n(v_key_5928_, 2);
                    v_val_5929_ = crate::leanh::lean_ctor_get(v_x_5926_, 2);
                    crate::leanh::lean_inc(v_val_5929_);
                    v_rchild_5930_ = crate::leanh::lean_ctor_get(v_x_5926_, 3);
                    crate::leanh::lean_inc(v_rchild_5930_);
                    crate::leanh::lean_dec_ref_known(v_x_5926_, 4);
                    crate::leanh::lean_inc(v_mergeFn_5924_);
                    crate::leanh::lean_inc_ref_n(v_cmp_5923_, 2);
                    crate::leanh::lean_inc_n(v_t_u2082_5922_, 2);
                    v_val_5931_ =
                        l_Lean_RBNode_fold___at___00Lean_RBMap_intersectBy_spec__0___redArg(
                            v_t_u2082_5922_,
                            v_cmp_5923_,
                            v_mergeFn_5924_,
                            v_x_5925_,
                            v_lchild_5927_,
                        );
                    v___x_5932_ = l_Lean_RBNode_find___at___00Lean_RBMap_mergeBy_spec__1___redArg(
                        v_cmp_5923_,
                        v_t_u2082_5922_,
                        v_key_5928_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_5932_) == 0 {
                        crate::leanh::lean_dec(v_val_5929_);
                        crate::leanh::lean_dec(v_key_5928_);
                        v_x_5925_ = v_val_5931_;
                        v_x_5926_ = v_rchild_5930_;
                        state = 0;
                        continue;
                    } else {
                        v_val_5934_ = crate::leanh::lean_ctor_get(v___x_5932_, 0);
                        crate::leanh::lean_inc(v_val_5934_);
                        crate::leanh::lean_dec_ref_known(v___x_5932_, 1);
                        crate::leanh::lean_inc(v_mergeFn_5924_);
                        crate::leanh::lean_inc(v_key_5928_);
                        v___x_5935_ = crate::leanh::lean_apply_3(
                            v_mergeFn_5924_,
                            v_key_5928_,
                            v_val_5929_,
                            v_val_5934_,
                        );
                        crate::leanh::lean_inc_ref(v_cmp_5923_);
                        v___x_5936_ =
                            l_Lean_RBNode_insert___at___00Lean_RBMap_mergeBy_spec__0___redArg(
                                v_cmp_5923_,
                                v_val_5931_,
                                v_key_5928_,
                                v___x_5935_,
                            );
                        v_x_5925_ = v___x_5936_;
                        v_x_5926_ = v_rchild_5930_;
                        state = 0;
                        continue;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_RBMap_intersectBy___redArg(
    mut v_cmp_5938_: *mut crate::leanh::LeanObject,
    mut v_mergeFn_5939_: *mut crate::leanh::LeanObject,
    mut v_t_u2081_5940_: *mut crate::leanh::LeanObject,
    mut v_t_u2082_5941_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5942_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5943_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5942_ = crate::leanh::lean_box(0);
    v___x_5943_ = l_Lean_RBNode_fold___at___00Lean_RBMap_intersectBy_spec__0___redArg(
        v_t_u2082_5941_,
        v_cmp_5938_,
        v_mergeFn_5939_,
        v___x_5942_,
        v_t_u2081_5940_,
    );
    return v___x_5943_;
}
pub unsafe fn l_Lean_RBMap_intersectBy(
    mut v_00_u03b1_5944_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_5945_: *mut crate::leanh::LeanObject,
    mut v_cmp_5946_: *mut crate::leanh::LeanObject,
    mut v_00_u03b3_5947_: *mut crate::leanh::LeanObject,
    mut v_00_u03b4_5948_: *mut crate::leanh::LeanObject,
    mut v_mergeFn_5949_: *mut crate::leanh::LeanObject,
    mut v_t_u2081_5950_: *mut crate::leanh::LeanObject,
    mut v_t_u2082_5951_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5952_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5952_ = l_Lean_RBMap_intersectBy___redArg(
        v_cmp_5946_,
        v_mergeFn_5949_,
        v_t_u2081_5950_,
        v_t_u2082_5951_,
    );
    return v___x_5952_;
}
pub unsafe fn l_Lean_RBNode_fold___at___00Lean_RBMap_intersectBy_spec__0(
    mut v_00_u03b1_5953_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_5954_: *mut crate::leanh::LeanObject,
    mut v_00_u03b4_5955_: *mut crate::leanh::LeanObject,
    mut v_00_u03b3_5956_: *mut crate::leanh::LeanObject,
    mut v_t_u2082_5957_: *mut crate::leanh::LeanObject,
    mut v_cmp_5958_: *mut crate::leanh::LeanObject,
    mut v_mergeFn_5959_: *mut crate::leanh::LeanObject,
    mut v_x_5960_: *mut crate::leanh::LeanObject,
    mut v_x_5961_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5962_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5962_ = l_Lean_RBNode_fold___at___00Lean_RBMap_intersectBy_spec__0___redArg(
        v_t_u2082_5957_,
        v_cmp_5958_,
        v_mergeFn_5959_,
        v_x_5960_,
        v_x_5961_,
    );
    return v___x_5962_;
}
pub unsafe fn l_Lean_RBNode_fold___at___00Lean_RBMap_filter_spec__0___redArg(
    mut v_f_5963_: *mut crate::leanh::LeanObject,
    mut v_cmp_5964_: *mut crate::leanh::LeanObject,
    mut v_x_5965_: *mut crate::leanh::LeanObject,
    mut v_x_5966_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_lchild_5967_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_key_5968_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_5969_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_rchild_5970_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_5971_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5972_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5973_: u8 = 0;
    let mut v___x_5975_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_5966_) == 0 {
                    crate::leanh::lean_dec_ref(v_cmp_5964_);
                    crate::leanh::lean_dec_ref(v_f_5963_);
                    return v_x_5965_;
                } else {
                    v_lchild_5967_ = crate::leanh::lean_ctor_get(v_x_5966_, 0);
                    crate::leanh::lean_inc(v_lchild_5967_);
                    v_key_5968_ = crate::leanh::lean_ctor_get(v_x_5966_, 1);
                    crate::leanh::lean_inc_n(v_key_5968_, 2);
                    v_val_5969_ = crate::leanh::lean_ctor_get(v_x_5966_, 2);
                    crate::leanh::lean_inc_n(v_val_5969_, 2);
                    v_rchild_5970_ = crate::leanh::lean_ctor_get(v_x_5966_, 3);
                    crate::leanh::lean_inc(v_rchild_5970_);
                    crate::leanh::lean_dec_ref_known(v_x_5966_, 4);
                    crate::leanh::lean_inc_ref(v_cmp_5964_);
                    crate::leanh::lean_inc_ref_n(v_f_5963_, 2);
                    v_val_5971_ = l_Lean_RBNode_fold___at___00Lean_RBMap_filter_spec__0___redArg(
                        v_f_5963_,
                        v_cmp_5964_,
                        v_x_5965_,
                        v_lchild_5967_,
                    );
                    v___x_5972_ = crate::leanh::lean_apply_2(v_f_5963_, v_key_5968_, v_val_5969_);
                    v___x_5973_ = (crate::leanh::lean_unbox(v___x_5972_) as u8);
                    if v___x_5973_ == 0 {
                        crate::leanh::lean_dec(v_val_5969_);
                        crate::leanh::lean_dec(v_key_5968_);
                        v_x_5965_ = v_val_5971_;
                        v_x_5966_ = v_rchild_5970_;
                        state = 0;
                        continue;
                    } else {
                        crate::leanh::lean_inc_ref(v_cmp_5964_);
                        v___x_5975_ =
                            l_Lean_RBNode_insert___at___00Lean_RBMap_mergeBy_spec__0___redArg(
                                v_cmp_5964_,
                                v_val_5971_,
                                v_key_5968_,
                                v_val_5969_,
                            );
                        v_x_5965_ = v___x_5975_;
                        v_x_5966_ = v_rchild_5970_;
                        state = 0;
                        continue;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_RBMap_filter___redArg(
    mut v_cmp_5977_: *mut crate::leanh::LeanObject,
    mut v_f_5978_: *mut crate::leanh::LeanObject,
    mut v_m_5979_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5980_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5981_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5980_ = crate::leanh::lean_box(0);
    v___x_5981_ = l_Lean_RBNode_fold___at___00Lean_RBMap_filter_spec__0___redArg(
        v_f_5978_,
        v_cmp_5977_,
        v___x_5980_,
        v_m_5979_,
    );
    return v___x_5981_;
}
pub unsafe fn l_Lean_RBMap_filter(
    mut v_00_u03b1_5982_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_5983_: *mut crate::leanh::LeanObject,
    mut v_cmp_5984_: *mut crate::leanh::LeanObject,
    mut v_f_5985_: *mut crate::leanh::LeanObject,
    mut v_m_5986_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5987_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5987_ = l_Lean_RBMap_filter___redArg(v_cmp_5984_, v_f_5985_, v_m_5986_);
    return v___x_5987_;
}
pub unsafe fn l_Lean_RBNode_fold___at___00Lean_RBMap_filter_spec__0(
    mut v_00_u03b1_5988_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_5989_: *mut crate::leanh::LeanObject,
    mut v_f_5990_: *mut crate::leanh::LeanObject,
    mut v_cmp_5991_: *mut crate::leanh::LeanObject,
    mut v_x_5992_: *mut crate::leanh::LeanObject,
    mut v_x_5993_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5994_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5994_ = l_Lean_RBNode_fold___at___00Lean_RBMap_filter_spec__0___redArg(
        v_f_5990_,
        v_cmp_5991_,
        v_x_5992_,
        v_x_5993_,
    );
    return v___x_5994_;
}
pub unsafe fn l_Lean_RBNode_fold___at___00Lean_RBMap_filterMap_spec__0___redArg(
    mut v_f_5995_: *mut crate::leanh::LeanObject,
    mut v_cmp_5996_: *mut crate::leanh::LeanObject,
    mut v_x_5997_: *mut crate::leanh::LeanObject,
    mut v_x_5998_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_lchild_5999_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_key_6000_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_6001_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_rchild_6002_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_6003_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6004_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_6006_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6007_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_5998_) == 0 {
                    crate::leanh::lean_dec_ref(v_cmp_5996_);
                    crate::leanh::lean_dec_ref(v_f_5995_);
                    return v_x_5997_;
                } else {
                    v_lchild_5999_ = crate::leanh::lean_ctor_get(v_x_5998_, 0);
                    crate::leanh::lean_inc(v_lchild_5999_);
                    v_key_6000_ = crate::leanh::lean_ctor_get(v_x_5998_, 1);
                    crate::leanh::lean_inc_n(v_key_6000_, 2);
                    v_val_6001_ = crate::leanh::lean_ctor_get(v_x_5998_, 2);
                    crate::leanh::lean_inc(v_val_6001_);
                    v_rchild_6002_ = crate::leanh::lean_ctor_get(v_x_5998_, 3);
                    crate::leanh::lean_inc(v_rchild_6002_);
                    crate::leanh::lean_dec_ref_known(v_x_5998_, 4);
                    crate::leanh::lean_inc_ref(v_cmp_5996_);
                    crate::leanh::lean_inc_ref_n(v_f_5995_, 2);
                    v_val_6003_ = l_Lean_RBNode_fold___at___00Lean_RBMap_filterMap_spec__0___redArg(
                        v_f_5995_,
                        v_cmp_5996_,
                        v_x_5997_,
                        v_lchild_5999_,
                    );
                    v___x_6004_ = crate::leanh::lean_apply_2(v_f_5995_, v_key_6000_, v_val_6001_);
                    if crate::leanh::lean_obj_tag(v___x_6004_) == 0 {
                        crate::leanh::lean_dec(v_key_6000_);
                        v_x_5997_ = v_val_6003_;
                        v_x_5998_ = v_rchild_6002_;
                        state = 0;
                        continue;
                    } else {
                        v_val_6006_ = crate::leanh::lean_ctor_get(v___x_6004_, 0);
                        crate::leanh::lean_inc(v_val_6006_);
                        crate::leanh::lean_dec_ref_known(v___x_6004_, 1);
                        crate::leanh::lean_inc_ref(v_cmp_5996_);
                        v___x_6007_ =
                            l_Lean_RBNode_insert___at___00Lean_RBMap_mergeBy_spec__0___redArg(
                                v_cmp_5996_,
                                v_val_6003_,
                                v_key_6000_,
                                v_val_6006_,
                            );
                        v_x_5997_ = v___x_6007_;
                        v_x_5998_ = v_rchild_6002_;
                        state = 0;
                        continue;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_RBMap_filterMap___redArg(
    mut v_cmp_6009_: *mut crate::leanh::LeanObject,
    mut v_f_6010_: *mut crate::leanh::LeanObject,
    mut v_m_6011_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6012_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6013_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6012_ = crate::leanh::lean_box(0);
    v___x_6013_ = l_Lean_RBNode_fold___at___00Lean_RBMap_filterMap_spec__0___redArg(
        v_f_6010_,
        v_cmp_6009_,
        v___x_6012_,
        v_m_6011_,
    );
    return v___x_6013_;
}
pub unsafe fn l_Lean_RBMap_filterMap(
    mut v_00_u03b1_6014_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_6015_: *mut crate::leanh::LeanObject,
    mut v_cmp_6016_: *mut crate::leanh::LeanObject,
    mut v_00_u03b3_6017_: *mut crate::leanh::LeanObject,
    mut v_f_6018_: *mut crate::leanh::LeanObject,
    mut v_m_6019_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6020_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6020_ = l_Lean_RBMap_filterMap___redArg(v_cmp_6016_, v_f_6018_, v_m_6019_);
    return v___x_6020_;
}
pub unsafe fn l_Lean_RBNode_fold___at___00Lean_RBMap_filterMap_spec__0(
    mut v_00_u03b1_6021_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_6022_: *mut crate::leanh::LeanObject,
    mut v_00_u03b3_6023_: *mut crate::leanh::LeanObject,
    mut v_f_6024_: *mut crate::leanh::LeanObject,
    mut v_cmp_6025_: *mut crate::leanh::LeanObject,
    mut v_x_6026_: *mut crate::leanh::LeanObject,
    mut v_x_6027_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6028_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6028_ = l_Lean_RBNode_fold___at___00Lean_RBMap_filterMap_spec__0___redArg(
        v_f_6024_,
        v_cmp_6025_,
        v_x_6026_,
        v_x_6027_,
    );
    return v___x_6028_;
}
pub unsafe fn l_List_foldl___at___00Lean_rbmapOf_spec__0___redArg(
    mut v_cmp_6029_: *mut crate::leanh::LeanObject,
    mut v_x_6030_: *mut crate::leanh::LeanObject,
    mut v_x_6031_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_head_6032_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_6033_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_6034_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_6035_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6036_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_6031_) == 0 {
                    crate::leanh::lean_dec_ref(v_cmp_6029_);
                    return v_x_6030_;
                } else {
                    v_head_6032_ = crate::leanh::lean_ctor_get(v_x_6031_, 0);
                    crate::leanh::lean_inc(v_head_6032_);
                    v_tail_6033_ = crate::leanh::lean_ctor_get(v_x_6031_, 1);
                    crate::leanh::lean_inc(v_tail_6033_);
                    crate::leanh::lean_dec_ref_known(v_x_6031_, 2);
                    v_fst_6034_ = crate::leanh::lean_ctor_get(v_head_6032_, 0);
                    crate::leanh::lean_inc(v_fst_6034_);
                    v_snd_6035_ = crate::leanh::lean_ctor_get(v_head_6032_, 1);
                    crate::leanh::lean_inc(v_snd_6035_);
                    crate::leanh::lean_dec(v_head_6032_);
                    crate::leanh::lean_inc_ref(v_cmp_6029_);
                    v___x_6036_ = l_Lean_RBNode_insert___at___00Lean_RBMap_mergeBy_spec__0___redArg(
                        v_cmp_6029_,
                        v_x_6030_,
                        v_fst_6034_,
                        v_snd_6035_,
                    );
                    v_x_6030_ = v___x_6036_;
                    v_x_6031_ = v_tail_6033_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_rbmapOf___redArg(
    mut v_l_6038_: *mut crate::leanh::LeanObject,
    mut v_cmp_6039_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6040_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6041_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6040_ = crate::leanh::lean_box(0);
    v___x_6041_ =
        l_List_foldl___at___00Lean_rbmapOf_spec__0___redArg(v_cmp_6039_, v___x_6040_, v_l_6038_);
    return v___x_6041_;
}
pub unsafe fn l_Lean_rbmapOf(
    mut v_00_u03b1_6042_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_6043_: *mut crate::leanh::LeanObject,
    mut v_l_6044_: *mut crate::leanh::LeanObject,
    mut v_cmp_6045_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6046_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6046_ = l_Lean_rbmapOf___redArg(v_l_6044_, v_cmp_6045_);
    return v___x_6046_;
}
pub unsafe fn l_List_foldl___at___00Lean_rbmapOf_spec__0(
    mut v_00_u03b1_6047_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_6048_: *mut crate::leanh::LeanObject,
    mut v_cmp_6049_: *mut crate::leanh::LeanObject,
    mut v_x_6050_: *mut crate::leanh::LeanObject,
    mut v_x_6051_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6052_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6052_ =
        l_List_foldl___at___00Lean_rbmapOf_spec__0___redArg(v_cmp_6049_, v_x_6050_, v_x_6051_);
    return v___x_6052_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Data_RBMap(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Init_Data_Ord_Basic(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Nat_Linear(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Array_Basic(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_WFTactics(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Data_RBMap(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_meta_initialized = true;
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lean_Data_RBMap(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Init_Data_Ord_Basic(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Data_Nat_Linear(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Data_Array_Basic(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_WFTactics(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Data_RBMap(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Lean_Data_RBMap(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Lean_Data_RBMap(builtin);
}
