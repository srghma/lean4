// Lean compiler output
// Module: Init.System.ST
// Imports: Init.Control.Except Init.NotationExtra Init.Classical
use crate::ffi::{
    lean_st_mk_ref, lean_st_ref_get, lean_st_ref_ptr_eq, lean_st_ref_set, lean_st_ref_swap,
    lean_st_ref_take, lean_void_mk,
};
use crate::r#gen::Init::Classical::{initialize_Init_Classical, runtime_initialize_Init_Classical};
use crate::r#gen::Init::Control::Except::{
    initialize_Init_Control_Except, runtime_initialize_Init_Control_Except,
};
use crate::r#gen::Init::NotationExtra::{
    initialize_Init_NotationExtra, runtime_initialize_Init_NotationExtra,
};
pub static l_instMonadST___closed__0_value: leanh::LeanClosureObject<0> =
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
        m_fun: l_instMonadST___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 5,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_instMonadST___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_instMonadST___closed__0_value) as *mut leanh::LeanObject;
pub static l_instMonadST___closed__1_value: leanh::LeanClosureObject<0> =
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
        m_fun: l_instMonadST___lam__1___boxed as *const core::ffi::c_void,
        m_arity: 5,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_instMonadST___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_instMonadST___closed__1_value) as *mut leanh::LeanObject;
pub static l_instMonadST___closed__2_value: leanh::LeanClosureObject<0> =
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
        m_fun: l_instMonadST___lam__2___boxed as *const core::ffi::c_void,
        m_arity: 3,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_instMonadST___closed__2: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_instMonadST___closed__2_value) as *mut leanh::LeanObject;
pub static l_instMonadST___closed__3_value: leanh::LeanClosureObject<0> =
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
        m_fun: l_instMonadST___lam__3___boxed as *const core::ffi::c_void,
        m_arity: 5,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_instMonadST___closed__3: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_instMonadST___closed__3_value) as *mut leanh::LeanObject;
pub static l_instMonadST___closed__4_value: leanh::LeanClosureObject<0> =
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
        m_fun: l_instMonadST___lam__4___boxed as *const core::ffi::c_void,
        m_arity: 5,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_instMonadST___closed__4: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_instMonadST___closed__4_value) as *mut leanh::LeanObject;
pub static l_instMonadST___closed__5_value: leanh::LeanClosureObject<0> =
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
        m_fun: l_instMonadST___lam__5___boxed as *const core::ffi::c_void,
        m_arity: 5,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_instMonadST___closed__5: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_instMonadST___closed__5_value) as *mut leanh::LeanObject;
pub static l_instMonadST___closed__6_value: leanh::LeanCtorObject<2> =
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
            core::ptr::addr_of!(l_instMonadST___closed__0_value) as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_instMonadST___closed__1_value) as *mut leanh::LeanObject,
        ],
    };
static mut l_instMonadST___closed__6: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_instMonadST___closed__6_value) as *mut leanh::LeanObject;
pub static l_instMonadST___closed__7_value: leanh::LeanCtorObject<5> =
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
            core::ptr::addr_of!(l_instMonadST___closed__6_value) as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_instMonadST___closed__2_value) as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_instMonadST___closed__3_value) as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_instMonadST___closed__4_value) as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_instMonadST___closed__5_value) as *mut leanh::LeanObject,
        ],
    };
static mut l_instMonadST___closed__7: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_instMonadST___closed__7_value) as *mut leanh::LeanObject;
pub static l_instMonadST___closed__8_value: leanh::LeanClosureObject<1> =
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
        m_fun: l_ST_bind___boxed as *const core::ffi::c_void,
        m_arity: 6,
        m_num_fixed: 1,
        m_objs: [(((0 as usize) << 1) | 1) as *mut leanh::LeanObject],
    };
static mut l_instMonadST___closed__8: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_instMonadST___closed__8_value) as *mut leanh::LeanObject;
pub static l_instMonadST___closed__9_value: leanh::LeanCtorObject<2> =
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
            core::ptr::addr_of!(l_instMonadST___closed__7_value) as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_instMonadST___closed__8_value) as *mut leanh::LeanObject,
        ],
    };
static mut l_instMonadST___closed__9: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_instMonadST___closed__9_value) as *mut leanh::LeanObject;
pub static l_instMonadFinallyST___closed__0_value: leanh::LeanClosureObject<0> =
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
        m_fun: l_instMonadFinallyST___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 5,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_instMonadFinallyST___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_instMonadFinallyST___closed__0_value) as *mut leanh::LeanObject;
pub static l_instMonadAttachST___closed__0_value: leanh::LeanClosureObject<0> =
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
        m_fun: l_instMonadAttachST___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 3,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_instMonadAttachST___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_instMonadAttachST___closed__0_value) as *mut leanh::LeanObject;
pub static l_instMonadEST___closed__0_value: leanh::LeanClosureObject<0> =
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
        m_fun: l_instMonadEST___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 5,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_instMonadEST___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_instMonadEST___closed__0_value) as *mut leanh::LeanObject;
pub static l_instMonadEST___closed__1_value: leanh::LeanClosureObject<0> =
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
        m_fun: l_instMonadEST___lam__1___boxed as *const core::ffi::c_void,
        m_arity: 5,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_instMonadEST___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_instMonadEST___closed__1_value) as *mut leanh::LeanObject;
pub static l_instMonadEST___closed__2_value: leanh::LeanClosureObject<0> =
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
        m_fun: l_instMonadEST___lam__2___boxed as *const core::ffi::c_void,
        m_arity: 3,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_instMonadEST___closed__2: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_instMonadEST___closed__2_value) as *mut leanh::LeanObject;
pub static l_instMonadEST___closed__3_value: leanh::LeanClosureObject<0> =
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
        m_fun: l_instMonadEST___lam__3___boxed as *const core::ffi::c_void,
        m_arity: 5,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_instMonadEST___closed__3: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_instMonadEST___closed__3_value) as *mut leanh::LeanObject;
pub static l_instMonadEST___closed__4_value: leanh::LeanClosureObject<0> =
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
        m_fun: l_instMonadEST___lam__4___boxed as *const core::ffi::c_void,
        m_arity: 5,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_instMonadEST___closed__4: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_instMonadEST___closed__4_value) as *mut leanh::LeanObject;
pub static l_instMonadEST___closed__5_value: leanh::LeanClosureObject<0> =
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
        m_fun: l_instMonadEST___lam__5___boxed as *const core::ffi::c_void,
        m_arity: 5,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_instMonadEST___closed__5: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_instMonadEST___closed__5_value) as *mut leanh::LeanObject;
pub static l_instMonadEST___closed__6_value: leanh::LeanCtorObject<2> =
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
            core::ptr::addr_of!(l_instMonadEST___closed__0_value) as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_instMonadEST___closed__1_value) as *mut leanh::LeanObject,
        ],
    };
static mut l_instMonadEST___closed__6: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_instMonadEST___closed__6_value) as *mut leanh::LeanObject;
pub static l_instMonadEST___closed__7_value: leanh::LeanCtorObject<5> =
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
            core::ptr::addr_of!(l_instMonadEST___closed__6_value) as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_instMonadEST___closed__2_value) as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_instMonadEST___closed__3_value) as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_instMonadEST___closed__4_value) as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_instMonadEST___closed__5_value) as *mut leanh::LeanObject,
        ],
    };
static mut l_instMonadEST___closed__7: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_instMonadEST___closed__7_value) as *mut leanh::LeanObject;
pub static l_instMonadEST___closed__8_value: leanh::LeanClosureObject<2> =
    leanh::LeanClosureObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut leanh::LeanObject>() * 2)
                as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_EST_bind___boxed as *const core::ffi::c_void,
        m_arity: 7,
        m_num_fixed: 2,
        m_objs: [
            (((0 as usize) << 1) | 1) as *mut leanh::LeanObject,
            (((0 as usize) << 1) | 1) as *mut leanh::LeanObject,
        ],
    };
static mut l_instMonadEST___closed__8: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_instMonadEST___closed__8_value) as *mut leanh::LeanObject;
pub static l_instMonadEST___closed__9_value: leanh::LeanCtorObject<2> =
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
            core::ptr::addr_of!(l_instMonadEST___closed__7_value) as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_instMonadEST___closed__8_value) as *mut leanh::LeanObject,
        ],
    };
static mut l_instMonadEST___closed__9: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_instMonadEST___closed__9_value) as *mut leanh::LeanObject;
pub static l_instMonadFinallyEST___closed__0_value: leanh::LeanClosureObject<0> =
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
        m_fun: l_instMonadFinallyEST___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 5,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_instMonadFinallyEST___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_instMonadFinallyEST___closed__0_value) as *mut leanh::LeanObject;
pub static l_instMonadAttachEST___closed__0_value: leanh::LeanClosureObject<0> =
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
        m_fun: l_instMonadAttachEST___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 3,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_instMonadAttachEST___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_instMonadAttachEST___closed__0_value) as *mut leanh::LeanObject;
pub static l_instMonadExceptOfEST___closed__0_value: leanh::LeanClosureObject<2> =
    leanh::LeanClosureObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut leanh::LeanObject>() * 2)
                as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_EST_throw___boxed as *const core::ffi::c_void,
        m_arity: 5,
        m_num_fixed: 2,
        m_objs: [
            (((0 as usize) << 1) | 1) as *mut leanh::LeanObject,
            (((0 as usize) << 1) | 1) as *mut leanh::LeanObject,
        ],
    };
static mut l_instMonadExceptOfEST___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_instMonadExceptOfEST___closed__0_value) as *mut leanh::LeanObject;
pub static l_instMonadExceptOfEST___closed__1_value: leanh::LeanClosureObject<2> =
    leanh::LeanClosureObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut leanh::LeanObject>() * 2)
                as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_EST_tryCatch___boxed as *const core::ffi::c_void,
        m_arity: 6,
        m_num_fixed: 2,
        m_objs: [
            (((0 as usize) << 1) | 1) as *mut leanh::LeanObject,
            (((0 as usize) << 1) | 1) as *mut leanh::LeanObject,
        ],
    };
static mut l_instMonadExceptOfEST___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_instMonadExceptOfEST___closed__1_value) as *mut leanh::LeanObject;
pub static l_instMonadExceptOfEST___closed__2_value: leanh::LeanCtorObject<2> =
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
            core::ptr::addr_of!(l_instMonadExceptOfEST___closed__0_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_instMonadExceptOfEST___closed__1_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_instMonadExceptOfEST___closed__2: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_instMonadExceptOfEST___closed__2_value) as *mut leanh::LeanObject;
pub static l_instMonadLiftSTEST___closed__0_value: leanh::LeanClosureObject<0> =
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
        m_fun: l_instMonadLiftSTEST___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 3,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_instMonadLiftSTEST___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_instMonadLiftSTEST___closed__0_value) as *mut leanh::LeanObject;
pub static mut l_ST_RefPointed: *mut leanh::LeanObject = core::ptr::null_mut();
pub unsafe fn l_Void_nonemptyType(
    mut v_00_u03c3_932_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_933_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_933_ = leanh::lean_box(0);
    return v___x_933_;
}
pub unsafe fn l_Void_mk___boxed(
    mut v_00_u03c3_936_: *mut leanh::LeanObject,
    mut v_x_937_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_938_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_938_ = lean_void_mk(v_x_937_);
    return v_res_938_;
}
pub unsafe fn l_ST_pure___redArg(
    mut v_x_939_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    leanh::lean_inc(v_x_939_);
    return v_x_939_;
}
pub unsafe fn l_ST_pure___redArg___boxed(
    mut v_x_941_: *mut leanh::LeanObject,
    mut v_s_942_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_943_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_943_ = l_ST_pure___redArg(v_x_941_);
    leanh::lean_dec(v_x_941_);
    return v_res_943_;
}
pub unsafe fn l_ST_pure(
    mut v_00_u03b1_944_: *mut leanh::LeanObject,
    mut v_00_u03c3_945_: *mut leanh::LeanObject,
    mut v_x_946_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    leanh::lean_inc(v_x_946_);
    return v_x_946_;
}
pub unsafe fn l_ST_pure___boxed(
    mut v_00_u03b1_948_: *mut leanh::LeanObject,
    mut v_00_u03c3_949_: *mut leanh::LeanObject,
    mut v_x_950_: *mut leanh::LeanObject,
    mut v_s_951_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_952_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_952_ = l_ST_pure(v_00_u03b1_948_, v_00_u03c3_949_, v_x_950_);
    leanh::lean_dec(v_x_950_);
    return v_res_952_;
}
pub unsafe fn l_ST_bind___redArg(
    mut v_x_953_: *mut leanh::LeanObject,
    mut v_f_954_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_956_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_957_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_956_ = leanh::lean_apply_1(v_x_953_, leanh::lean_box(0));
    v___x_957_ = leanh::lean_apply_2(v_f_954_, v___x_956_, leanh::lean_box(0));
    return v___x_957_;
}
pub unsafe fn l_ST_bind___redArg___boxed(
    mut v_x_958_: *mut leanh::LeanObject,
    mut v_f_959_: *mut leanh::LeanObject,
    mut v_s_960_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_961_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_961_ = l_ST_bind___redArg(v_x_958_, v_f_959_);
    return v_res_961_;
}
pub unsafe fn l_ST_bind(
    mut v_00_u03c3_962_: *mut leanh::LeanObject,
    mut v_00_u03b1_963_: *mut leanh::LeanObject,
    mut v_00_u03b2_964_: *mut leanh::LeanObject,
    mut v_x_965_: *mut leanh::LeanObject,
    mut v_f_966_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_968_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_969_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_968_ = leanh::lean_apply_1(v_x_965_, leanh::lean_box(0));
    v___x_969_ = leanh::lean_apply_2(v_f_966_, v___x_968_, leanh::lean_box(0));
    return v___x_969_;
}
pub unsafe fn l_ST_bind___boxed(
    mut v_00_u03c3_970_: *mut leanh::LeanObject,
    mut v_00_u03b1_971_: *mut leanh::LeanObject,
    mut v_00_u03b2_972_: *mut leanh::LeanObject,
    mut v_x_973_: *mut leanh::LeanObject,
    mut v_f_974_: *mut leanh::LeanObject,
    mut v_s_975_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_976_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_976_ = l_ST_bind(
        v_00_u03c3_970_,
        v_00_u03b1_971_,
        v_00_u03b2_972_,
        v_x_973_,
        v_f_974_,
    );
    return v_res_976_;
}
pub unsafe fn l_instMonadST___lam__0(
    mut v_00_u03b1_977_: *mut leanh::LeanObject,
    mut v_00_u03b2_978_: *mut leanh::LeanObject,
    mut v_f_979_: *mut leanh::LeanObject,
    mut v_x_980_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_982_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_983_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_982_ = leanh::lean_apply_1(v_x_980_, leanh::lean_box(0));
    v___x_983_ = leanh::lean_apply_1(v_f_979_, v___x_982_);
    return v___x_983_;
}
pub unsafe fn l_instMonadST___lam__0___boxed(
    mut v_00_u03b1_984_: *mut leanh::LeanObject,
    mut v_00_u03b2_985_: *mut leanh::LeanObject,
    mut v_f_986_: *mut leanh::LeanObject,
    mut v_x_987_: *mut leanh::LeanObject,
    mut v___y_988_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_989_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_989_ = l_instMonadST___lam__0(v_00_u03b1_984_, v_00_u03b2_985_, v_f_986_, v_x_987_);
    return v_res_989_;
}
pub unsafe fn l_instMonadST___lam__1(
    mut v_00_u03b1_990_: *mut leanh::LeanObject,
    mut v_00_u03b2_991_: *mut leanh::LeanObject,
    mut v___y_992_: *mut leanh::LeanObject,
    mut v___y_993_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_995_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_995_ = leanh::lean_apply_1(v___y_993_, leanh::lean_box(0));
    leanh::lean_dec(v___x_995_);
    leanh::lean_inc(v___y_992_);
    return v___y_992_;
}
pub unsafe fn l_instMonadST___lam__1___boxed(
    mut v_00_u03b1_996_: *mut leanh::LeanObject,
    mut v_00_u03b2_997_: *mut leanh::LeanObject,
    mut v___y_998_: *mut leanh::LeanObject,
    mut v___y_999_: *mut leanh::LeanObject,
    mut v___y_1000_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1001_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1001_ = l_instMonadST___lam__1(v_00_u03b1_996_, v_00_u03b2_997_, v___y_998_, v___y_999_);
    leanh::lean_dec(v___y_998_);
    return v_res_1001_;
}
pub unsafe fn l_instMonadST___lam__2(
    mut v_00_u03b1_1002_: *mut leanh::LeanObject,
    mut v___y_1003_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    leanh::lean_inc(v___y_1003_);
    return v___y_1003_;
}
pub unsafe fn l_instMonadST___lam__2___boxed(
    mut v_00_u03b1_1005_: *mut leanh::LeanObject,
    mut v___y_1006_: *mut leanh::LeanObject,
    mut v___y_1007_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1008_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1008_ = l_instMonadST___lam__2(v_00_u03b1_1005_, v___y_1006_);
    leanh::lean_dec(v___y_1006_);
    return v_res_1008_;
}
pub unsafe fn l_instMonadST___lam__3(
    mut v_00_u03b1_1009_: *mut leanh::LeanObject,
    mut v_00_u03b2_1010_: *mut leanh::LeanObject,
    mut v_f_1011_: *mut leanh::LeanObject,
    mut v_x_1012_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1014_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1015_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1016_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1017_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1014_ = leanh::lean_apply_1(v_f_1011_, leanh::lean_box(0));
    v___x_1015_ = leanh::lean_box(0);
    v___x_1016_ = leanh::lean_apply_2(v_x_1012_, v___x_1015_, leanh::lean_box(0));
    v___x_1017_ = leanh::lean_apply_1(v___x_1014_, v___x_1016_);
    return v___x_1017_;
}
pub unsafe fn l_instMonadST___lam__3___boxed(
    mut v_00_u03b1_1018_: *mut leanh::LeanObject,
    mut v_00_u03b2_1019_: *mut leanh::LeanObject,
    mut v_f_1020_: *mut leanh::LeanObject,
    mut v_x_1021_: *mut leanh::LeanObject,
    mut v___y_1022_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1023_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1023_ = l_instMonadST___lam__3(v_00_u03b1_1018_, v_00_u03b2_1019_, v_f_1020_, v_x_1021_);
    return v_res_1023_;
}
pub unsafe fn l_instMonadST___lam__4(
    mut v_00_u03b1_1024_: *mut leanh::LeanObject,
    mut v_00_u03b2_1025_: *mut leanh::LeanObject,
    mut v_x_1026_: *mut leanh::LeanObject,
    mut v_y_1027_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1029_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1030_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1031_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1029_ = leanh::lean_apply_1(v_x_1026_, leanh::lean_box(0));
    v___x_1030_ = leanh::lean_box(0);
    v___x_1031_ = leanh::lean_apply_2(v_y_1027_, v___x_1030_, leanh::lean_box(0));
    leanh::lean_dec(v___x_1031_);
    return v___x_1029_;
}
pub unsafe fn l_instMonadST___lam__4___boxed(
    mut v_00_u03b1_1032_: *mut leanh::LeanObject,
    mut v_00_u03b2_1033_: *mut leanh::LeanObject,
    mut v_x_1034_: *mut leanh::LeanObject,
    mut v_y_1035_: *mut leanh::LeanObject,
    mut v___y_1036_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1037_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1037_ = l_instMonadST___lam__4(v_00_u03b1_1032_, v_00_u03b2_1033_, v_x_1034_, v_y_1035_);
    return v_res_1037_;
}
pub unsafe fn l_instMonadST___lam__5(
    mut v_00_u03b1_1038_: *mut leanh::LeanObject,
    mut v_00_u03b2_1039_: *mut leanh::LeanObject,
    mut v_x_1040_: *mut leanh::LeanObject,
    mut v_y_1041_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1043_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1044_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1045_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1043_ = leanh::lean_apply_1(v_x_1040_, leanh::lean_box(0));
    leanh::lean_dec(v___x_1043_);
    v___x_1044_ = leanh::lean_box(0);
    v___x_1045_ = leanh::lean_apply_2(v_y_1041_, v___x_1044_, leanh::lean_box(0));
    return v___x_1045_;
}
pub unsafe fn l_instMonadST___lam__5___boxed(
    mut v_00_u03b1_1046_: *mut leanh::LeanObject,
    mut v_00_u03b2_1047_: *mut leanh::LeanObject,
    mut v_x_1048_: *mut leanh::LeanObject,
    mut v_y_1049_: *mut leanh::LeanObject,
    mut v___y_1050_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1051_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1051_ = l_instMonadST___lam__5(v_00_u03b1_1046_, v_00_u03b2_1047_, v_x_1048_, v_y_1049_);
    return v_res_1051_;
}
pub unsafe fn l_instMonadST(
    mut v_00_u03c3_1071_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1072_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1072_ = l_instMonadST___closed__9;
    return v___x_1072_;
}
pub unsafe fn l_instMonadFinallyST___lam__0(
    mut v_00_u03b1_1073_: *mut leanh::LeanObject,
    mut v_00_u03b2_1074_: *mut leanh::LeanObject,
    mut v_x_1075_: *mut leanh::LeanObject,
    mut v_f_1076_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1078_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1079_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1080_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1081_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1078_ = leanh::lean_apply_1(v_x_1075_, leanh::lean_box(0));
    leanh::lean_inc(v___x_1078_);
    v___x_1079_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_1079_, 0, v___x_1078_);
    v___x_1080_ = leanh::lean_apply_2(v_f_1076_, v___x_1079_, leanh::lean_box(0));
    v___x_1081_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_1081_, 0, v___x_1078_);
    leanh::lean_ctor_set(v___x_1081_, 1, v___x_1080_);
    return v___x_1081_;
}
pub unsafe fn l_instMonadFinallyST___lam__0___boxed(
    mut v_00_u03b1_1082_: *mut leanh::LeanObject,
    mut v_00_u03b2_1083_: *mut leanh::LeanObject,
    mut v_x_1084_: *mut leanh::LeanObject,
    mut v_f_1085_: *mut leanh::LeanObject,
    mut v_s_1086_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1087_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1087_ =
        l_instMonadFinallyST___lam__0(v_00_u03b1_1082_, v_00_u03b2_1083_, v_x_1084_, v_f_1085_);
    return v_res_1087_;
}
pub unsafe fn l_instMonadFinallyST(
    mut v_00_u03c3_1089_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_1090_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_1090_ = l_instMonadFinallyST___closed__0;
    return v___f_1090_;
}
pub unsafe fn l_instInhabitedST___redArg___lam__0(
    mut v_inst_1091_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    leanh::lean_inc(v_inst_1091_);
    return v_inst_1091_;
}
pub unsafe fn l_instInhabitedST___redArg___lam__0___boxed(
    mut v_inst_1093_: *mut leanh::LeanObject,
    mut v_s_1094_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1095_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1095_ = l_instInhabitedST___redArg___lam__0(v_inst_1093_);
    leanh::lean_dec(v_inst_1093_);
    return v_res_1095_;
}
pub unsafe fn l_instInhabitedST___redArg(
    mut v_inst_1096_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_1097_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_1097_ = leanh::lean_alloc_closure(
        l_instInhabitedST___redArg___lam__0___boxed as *mut core::ffi::c_void,
        2,
        1,
    );
    leanh::lean_closure_set(v___f_1097_, 0, v_inst_1096_);
    return v___f_1097_;
}
pub unsafe fn l_instInhabitedST(
    mut v_00_u03c3_1098_: *mut leanh::LeanObject,
    mut v_00_u03b1_1099_: *mut leanh::LeanObject,
    mut v_inst_1100_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_1101_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_1101_ = leanh::lean_alloc_closure(
        l_instInhabitedST___redArg___lam__0___boxed as *mut core::ffi::c_void,
        2,
        1,
    );
    leanh::lean_closure_set(v___f_1101_, 0, v_inst_1100_);
    return v___f_1101_;
}
pub unsafe fn l_instMonadAttachST___lam__0(
    mut v_00_u03b1_1102_: *mut leanh::LeanObject,
    mut v_x_1103_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1105_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1105_ = leanh::lean_apply_1(v_x_1103_, leanh::lean_box(0));
    return v___x_1105_;
}
pub unsafe fn l_instMonadAttachST___lam__0___boxed(
    mut v_00_u03b1_1106_: *mut leanh::LeanObject,
    mut v_x_1107_: *mut leanh::LeanObject,
    mut v_s_1108_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1109_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1109_ = l_instMonadAttachST___lam__0(v_00_u03b1_1106_, v_x_1107_);
    return v_res_1109_;
}
pub unsafe fn l_instMonadAttachST(
    mut v_00_u03c3_1111_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_1112_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_1112_ = l_instMonadAttachST___closed__0;
    return v___f_1112_;
}
pub unsafe fn l_EST_Out_ctorIdx___redArg(
    mut v_x_1113_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_x_1113_) == 0 {
        let mut v___x_1114_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_1114_ = leanh::lean_unsigned_to_nat(0);
        return v___x_1114_;
    } else {
        let mut v___x_1115_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_1115_ = leanh::lean_unsigned_to_nat(1);
        return v___x_1115_;
    }
}
pub unsafe fn l_EST_Out_ctorIdx___redArg___boxed(
    mut v_x_1116_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1117_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1117_ = l_EST_Out_ctorIdx___redArg(v_x_1116_);
    leanh::lean_dec_ref(v_x_1116_);
    return v_res_1117_;
}
pub unsafe fn l_EST_Out_ctorIdx(
    mut v_00_u03b5_1118_: *mut leanh::LeanObject,
    mut v_00_u03c3_1119_: *mut leanh::LeanObject,
    mut v_00_u03b1_1120_: *mut leanh::LeanObject,
    mut v_x_1121_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1122_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1122_ = l_EST_Out_ctorIdx___redArg(v_x_1121_);
    return v___x_1122_;
}
pub unsafe fn l_EST_Out_ctorIdx___boxed(
    mut v_00_u03b5_1123_: *mut leanh::LeanObject,
    mut v_00_u03c3_1124_: *mut leanh::LeanObject,
    mut v_00_u03b1_1125_: *mut leanh::LeanObject,
    mut v_x_1126_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1127_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1127_ = l_EST_Out_ctorIdx(
        v_00_u03b5_1123_,
        v_00_u03c3_1124_,
        v_00_u03b1_1125_,
        v_x_1126_,
    );
    leanh::lean_dec_ref(v_x_1126_);
    return v_res_1127_;
}
pub unsafe fn l_EST_Out_ctorElim___redArg(
    mut v_t_1128_: *mut leanh::LeanObject,
    mut v_k_1129_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_a_1130_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1131_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_a_1130_ = leanh::lean_ctor_get(v_t_1128_, 0);
    leanh::lean_inc(v_a_1130_);
    leanh::lean_dec_ref(v_t_1128_);
    v___x_1131_ = leanh::lean_apply_2(v_k_1129_, v_a_1130_, leanh::lean_box(0));
    return v___x_1131_;
}
pub unsafe fn l_EST_Out_ctorElim(
    mut v_00_u03b5_1132_: *mut leanh::LeanObject,
    mut v_00_u03c3_1133_: *mut leanh::LeanObject,
    mut v_00_u03b1_1134_: *mut leanh::LeanObject,
    mut v_motive_1135_: *mut leanh::LeanObject,
    mut v_ctorIdx_1136_: *mut leanh::LeanObject,
    mut v_t_1137_: *mut leanh::LeanObject,
    mut v_h_1138_: *mut leanh::LeanObject,
    mut v_k_1139_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1140_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1140_ = l_EST_Out_ctorElim___redArg(v_t_1137_, v_k_1139_);
    return v___x_1140_;
}
pub unsafe fn l_EST_Out_ctorElim___boxed(
    mut v_00_u03b5_1141_: *mut leanh::LeanObject,
    mut v_00_u03c3_1142_: *mut leanh::LeanObject,
    mut v_00_u03b1_1143_: *mut leanh::LeanObject,
    mut v_motive_1144_: *mut leanh::LeanObject,
    mut v_ctorIdx_1145_: *mut leanh::LeanObject,
    mut v_t_1146_: *mut leanh::LeanObject,
    mut v_h_1147_: *mut leanh::LeanObject,
    mut v_k_1148_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1149_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1149_ = l_EST_Out_ctorElim(
        v_00_u03b5_1141_,
        v_00_u03c3_1142_,
        v_00_u03b1_1143_,
        v_motive_1144_,
        v_ctorIdx_1145_,
        v_t_1146_,
        v_h_1147_,
        v_k_1148_,
    );
    leanh::lean_dec(v_ctorIdx_1145_);
    return v_res_1149_;
}
pub unsafe fn l_EST_Out_ok_elim___redArg(
    mut v_t_1150_: *mut leanh::LeanObject,
    mut v_ok_1151_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1152_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1152_ = l_EST_Out_ctorElim___redArg(v_t_1150_, v_ok_1151_);
    return v___x_1152_;
}
pub unsafe fn l_EST_Out_ok_elim(
    mut v_00_u03b5_1153_: *mut leanh::LeanObject,
    mut v_00_u03c3_1154_: *mut leanh::LeanObject,
    mut v_00_u03b1_1155_: *mut leanh::LeanObject,
    mut v_motive_1156_: *mut leanh::LeanObject,
    mut v_t_1157_: *mut leanh::LeanObject,
    mut v_h_1158_: *mut leanh::LeanObject,
    mut v_ok_1159_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1160_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1160_ = l_EST_Out_ctorElim___redArg(v_t_1157_, v_ok_1159_);
    return v___x_1160_;
}
pub unsafe fn l_EST_Out_error_elim___redArg(
    mut v_t_1161_: *mut leanh::LeanObject,
    mut v_error_1162_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1163_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1163_ = l_EST_Out_ctorElim___redArg(v_t_1161_, v_error_1162_);
    return v___x_1163_;
}
pub unsafe fn l_EST_Out_error_elim(
    mut v_00_u03b5_1164_: *mut leanh::LeanObject,
    mut v_00_u03c3_1165_: *mut leanh::LeanObject,
    mut v_00_u03b1_1166_: *mut leanh::LeanObject,
    mut v_motive_1167_: *mut leanh::LeanObject,
    mut v_t_1168_: *mut leanh::LeanObject,
    mut v_h_1169_: *mut leanh::LeanObject,
    mut v_error_1170_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1171_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1171_ = l_EST_Out_ctorElim___redArg(v_t_1168_, v_error_1170_);
    return v___x_1171_;
}
pub unsafe fn l_EST_pure___redArg(
    mut v_a_1172_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1174_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1174_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_1174_, 0, v_a_1172_);
    return v___x_1174_;
}
pub unsafe fn l_EST_pure___redArg___boxed(
    mut v_a_1175_: *mut leanh::LeanObject,
    mut v_s_1176_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1177_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1177_ = l_EST_pure___redArg(v_a_1175_);
    return v_res_1177_;
}
pub unsafe fn l_EST_pure(
    mut v_00_u03b1_1178_: *mut leanh::LeanObject,
    mut v_00_u03b5_1179_: *mut leanh::LeanObject,
    mut v_00_u03c3_1180_: *mut leanh::LeanObject,
    mut v_a_1181_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1183_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1183_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_1183_, 0, v_a_1181_);
    return v___x_1183_;
}
pub unsafe fn l_EST_pure___boxed(
    mut v_00_u03b1_1184_: *mut leanh::LeanObject,
    mut v_00_u03b5_1185_: *mut leanh::LeanObject,
    mut v_00_u03c3_1186_: *mut leanh::LeanObject,
    mut v_a_1187_: *mut leanh::LeanObject,
    mut v_s_1188_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1189_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1189_ = l_EST_pure(
        v_00_u03b1_1184_,
        v_00_u03b5_1185_,
        v_00_u03c3_1186_,
        v_a_1187_,
    );
    return v_res_1189_;
}
pub unsafe fn l_EST_bind___redArg(
    mut v_x_1190_: *mut leanh::LeanObject,
    mut v_f_1191_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1193_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1194_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1195_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1196_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1198_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1199_: u8 = 0;
    let mut v___x_1201_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1202_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1203_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1193_ = leanh::lean_apply_1(v_x_1190_, leanh::lean_box(0));
                if leanh::lean_obj_tag(v___x_1193_) == 0 {
                    v_a_1194_ = leanh::lean_ctor_get(v___x_1193_, 0);
                    leanh::lean_inc(v_a_1194_);
                    leanh::lean_dec_ref_known(v___x_1193_, 1);
                    v___x_1195_ =
                        leanh::lean_apply_2(v_f_1191_, v_a_1194_, leanh::lean_box(0));
                    return v___x_1195_;
                } else {
                    leanh::lean_dec_ref(v_f_1191_);
                    v_a_1196_ = leanh::lean_ctor_get(v___x_1193_, 0);
                    v_isSharedCheck_1203_ = (!leanh::lean_is_exclusive(v___x_1193_)) as u8;
                    if v_isSharedCheck_1203_ == 0 {
                        v___x_1198_ = v___x_1193_;
                        v_isShared_1199_ = v_isSharedCheck_1203_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_1196_);
                        leanh::lean_dec(v___x_1193_);
                        v___x_1198_ = leanh::lean_box(0);
                        v_isShared_1199_ = v_isSharedCheck_1203_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_1199_ == 0 {
                    v___x_1201_ = v___x_1198_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1202_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1202_, 0, v_a_1196_);
                    v___x_1201_ = v_reuseFailAlloc_1202_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1201_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_EST_bind___redArg___boxed(
    mut v_x_1204_: *mut leanh::LeanObject,
    mut v_f_1205_: *mut leanh::LeanObject,
    mut v_s_1206_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1207_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1207_ = l_EST_bind___redArg(v_x_1204_, v_f_1205_);
    return v_res_1207_;
}
pub unsafe fn l_EST_bind(
    mut v_00_u03b5_1208_: *mut leanh::LeanObject,
    mut v_00_u03c3_1209_: *mut leanh::LeanObject,
    mut v_00_u03b1_1210_: *mut leanh::LeanObject,
    mut v_00_u03b2_1211_: *mut leanh::LeanObject,
    mut v_x_1212_: *mut leanh::LeanObject,
    mut v_f_1213_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1215_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1216_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1217_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1218_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1220_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1221_: u8 = 0;
    let mut v___x_1223_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1224_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1225_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1215_ = leanh::lean_apply_1(v_x_1212_, leanh::lean_box(0));
                if leanh::lean_obj_tag(v___x_1215_) == 0 {
                    v_a_1216_ = leanh::lean_ctor_get(v___x_1215_, 0);
                    leanh::lean_inc(v_a_1216_);
                    leanh::lean_dec_ref_known(v___x_1215_, 1);
                    v___x_1217_ =
                        leanh::lean_apply_2(v_f_1213_, v_a_1216_, leanh::lean_box(0));
                    return v___x_1217_;
                } else {
                    leanh::lean_dec_ref(v_f_1213_);
                    v_a_1218_ = leanh::lean_ctor_get(v___x_1215_, 0);
                    v_isSharedCheck_1225_ = (!leanh::lean_is_exclusive(v___x_1215_)) as u8;
                    if v_isSharedCheck_1225_ == 0 {
                        v___x_1220_ = v___x_1215_;
                        v_isShared_1221_ = v_isSharedCheck_1225_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_1218_);
                        leanh::lean_dec(v___x_1215_);
                        v___x_1220_ = leanh::lean_box(0);
                        v_isShared_1221_ = v_isSharedCheck_1225_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_1221_ == 0 {
                    v___x_1223_ = v___x_1220_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1224_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1224_, 0, v_a_1218_);
                    v___x_1223_ = v_reuseFailAlloc_1224_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1223_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_EST_bind___boxed(
    mut v_00_u03b5_1226_: *mut leanh::LeanObject,
    mut v_00_u03c3_1227_: *mut leanh::LeanObject,
    mut v_00_u03b1_1228_: *mut leanh::LeanObject,
    mut v_00_u03b2_1229_: *mut leanh::LeanObject,
    mut v_x_1230_: *mut leanh::LeanObject,
    mut v_f_1231_: *mut leanh::LeanObject,
    mut v_s_1232_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1233_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1233_ = l_EST_bind(
        v_00_u03b5_1226_,
        v_00_u03c3_1227_,
        v_00_u03b1_1228_,
        v_00_u03b2_1229_,
        v_x_1230_,
        v_f_1231_,
    );
    return v_res_1233_;
}
pub unsafe fn l_EST_throw___redArg(
    mut v_e_1234_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1236_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1236_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_1236_, 0, v_e_1234_);
    return v___x_1236_;
}
pub unsafe fn l_EST_throw___redArg___boxed(
    mut v_e_1237_: *mut leanh::LeanObject,
    mut v_s_1238_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1239_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1239_ = l_EST_throw___redArg(v_e_1237_);
    return v_res_1239_;
}
pub unsafe fn l_EST_throw(
    mut v_00_u03b5_1240_: *mut leanh::LeanObject,
    mut v_00_u03c3_1241_: *mut leanh::LeanObject,
    mut v_00_u03b1_1242_: *mut leanh::LeanObject,
    mut v_e_1243_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1245_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1245_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_1245_, 0, v_e_1243_);
    return v___x_1245_;
}
pub unsafe fn l_EST_throw___boxed(
    mut v_00_u03b5_1246_: *mut leanh::LeanObject,
    mut v_00_u03c3_1247_: *mut leanh::LeanObject,
    mut v_00_u03b1_1248_: *mut leanh::LeanObject,
    mut v_e_1249_: *mut leanh::LeanObject,
    mut v_s_1250_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1251_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1251_ = l_EST_throw(
        v_00_u03b5_1246_,
        v_00_u03c3_1247_,
        v_00_u03b1_1248_,
        v_e_1249_,
    );
    return v_res_1251_;
}
pub unsafe fn l_EST_tryCatch___redArg(
    mut v_x_1252_: *mut leanh::LeanObject,
    mut v_handle_1253_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1255_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1255_ = leanh::lean_apply_1(v_x_1252_, leanh::lean_box(0));
    if leanh::lean_obj_tag(v___x_1255_) == 0 {
        leanh::lean_dec_ref(v_handle_1253_);
        return v___x_1255_;
    } else {
        let mut v_a_1256_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1257_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_a_1256_ = leanh::lean_ctor_get(v___x_1255_, 0);
        leanh::lean_inc(v_a_1256_);
        leanh::lean_dec_ref_known(v___x_1255_, 1);
        v___x_1257_ =
            leanh::lean_apply_2(v_handle_1253_, v_a_1256_, leanh::lean_box(0));
        return v___x_1257_;
    }
}
pub unsafe fn l_EST_tryCatch___redArg___boxed(
    mut v_x_1258_: *mut leanh::LeanObject,
    mut v_handle_1259_: *mut leanh::LeanObject,
    mut v_s_1260_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1261_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1261_ = l_EST_tryCatch___redArg(v_x_1258_, v_handle_1259_);
    return v_res_1261_;
}
pub unsafe fn l_EST_tryCatch(
    mut v_00_u03b5_1262_: *mut leanh::LeanObject,
    mut v_00_u03c3_1263_: *mut leanh::LeanObject,
    mut v_00_u03b1_1264_: *mut leanh::LeanObject,
    mut v_x_1265_: *mut leanh::LeanObject,
    mut v_handle_1266_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1268_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1268_ = leanh::lean_apply_1(v_x_1265_, leanh::lean_box(0));
    if leanh::lean_obj_tag(v___x_1268_) == 0 {
        leanh::lean_dec_ref(v_handle_1266_);
        return v___x_1268_;
    } else {
        let mut v_a_1269_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1270_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_a_1269_ = leanh::lean_ctor_get(v___x_1268_, 0);
        leanh::lean_inc(v_a_1269_);
        leanh::lean_dec_ref_known(v___x_1268_, 1);
        v___x_1270_ =
            leanh::lean_apply_2(v_handle_1266_, v_a_1269_, leanh::lean_box(0));
        return v___x_1270_;
    }
}
pub unsafe fn l_EST_tryCatch___boxed(
    mut v_00_u03b5_1271_: *mut leanh::LeanObject,
    mut v_00_u03c3_1272_: *mut leanh::LeanObject,
    mut v_00_u03b1_1273_: *mut leanh::LeanObject,
    mut v_x_1274_: *mut leanh::LeanObject,
    mut v_handle_1275_: *mut leanh::LeanObject,
    mut v_s_1276_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1277_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1277_ = l_EST_tryCatch(
        v_00_u03b5_1271_,
        v_00_u03c3_1272_,
        v_00_u03b1_1273_,
        v_x_1274_,
        v_handle_1275_,
    );
    return v_res_1277_;
}
pub unsafe fn l_instMonadEST___lam__0(
    mut v_00_u03b1_1278_: *mut leanh::LeanObject,
    mut v_00_u03b2_1279_: *mut leanh::LeanObject,
    mut v_f_1280_: *mut leanh::LeanObject,
    mut v_x_1281_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1283_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1284_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1286_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1287_: u8 = 0;
    let mut v___x_1288_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1290_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1291_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1292_: u8 = 0;
    let mut v_a_1293_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1295_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1296_: u8 = 0;
    let mut v___x_1298_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1299_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1300_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1283_ = leanh::lean_apply_1(v_x_1281_, leanh::lean_box(0));
                if leanh::lean_obj_tag(v___x_1283_) == 0 {
                    v_a_1284_ = leanh::lean_ctor_get(v___x_1283_, 0);
                    v_isSharedCheck_1292_ = (!leanh::lean_is_exclusive(v___x_1283_)) as u8;
                    if v_isSharedCheck_1292_ == 0 {
                        v___x_1286_ = v___x_1283_;
                        v_isShared_1287_ = v_isSharedCheck_1292_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_1284_);
                        leanh::lean_dec(v___x_1283_);
                        v___x_1286_ = leanh::lean_box(0);
                        v_isShared_1287_ = v_isSharedCheck_1292_;
                        state = 1;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v_f_1280_);
                    v_a_1293_ = leanh::lean_ctor_get(v___x_1283_, 0);
                    v_isSharedCheck_1300_ = (!leanh::lean_is_exclusive(v___x_1283_)) as u8;
                    if v_isSharedCheck_1300_ == 0 {
                        v___x_1295_ = v___x_1283_;
                        v_isShared_1296_ = v_isSharedCheck_1300_;
                        state = 3;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_1293_);
                        leanh::lean_dec(v___x_1283_);
                        v___x_1295_ = leanh::lean_box(0);
                        v_isShared_1296_ = v_isSharedCheck_1300_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v___x_1288_ = leanh::lean_apply_1(v_f_1280_, v_a_1284_);
                if v_isShared_1287_ == 0 {
                    leanh::lean_ctor_set(v___x_1286_, 0, v___x_1288_);
                    v___x_1290_ = v___x_1286_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1291_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1291_, 0, v___x_1288_);
                    v___x_1290_ = v_reuseFailAlloc_1291_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1290_;
            }
            3 => {
                if v_isShared_1296_ == 0 {
                    v___x_1298_ = v___x_1295_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1299_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1299_, 0, v_a_1293_);
                    v___x_1298_ = v_reuseFailAlloc_1299_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_1298_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_instMonadEST___lam__0___boxed(
    mut v_00_u03b1_1301_: *mut leanh::LeanObject,
    mut v_00_u03b2_1302_: *mut leanh::LeanObject,
    mut v_f_1303_: *mut leanh::LeanObject,
    mut v_x_1304_: *mut leanh::LeanObject,
    mut v___y_1305_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1306_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1306_ = l_instMonadEST___lam__0(v_00_u03b1_1301_, v_00_u03b2_1302_, v_f_1303_, v_x_1304_);
    return v_res_1306_;
}
pub unsafe fn l_instMonadEST___lam__1(
    mut v_00_u03b1_1307_: *mut leanh::LeanObject,
    mut v_00_u03b2_1308_: *mut leanh::LeanObject,
    mut v___y_1309_: *mut leanh::LeanObject,
    mut v___y_1310_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1312_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1314_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1315_: u8 = 0;
    let mut v___x_1317_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1318_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1319_: u8 = 0;
    let mut v_unused_1320_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1321_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1323_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1324_: u8 = 0;
    let mut v___x_1326_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1327_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1328_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1312_ = leanh::lean_apply_1(v___y_1310_, leanh::lean_box(0));
                if leanh::lean_obj_tag(v___x_1312_) == 0 {
                    v_isSharedCheck_1319_ = (!leanh::lean_is_exclusive(v___x_1312_)) as u8;
                    if v_isSharedCheck_1319_ == 0 {
                        v_unused_1320_ = leanh::lean_ctor_get(v___x_1312_, 0);
                        leanh::lean_dec(v_unused_1320_);
                        v___x_1314_ = v___x_1312_;
                        v_isShared_1315_ = v_isSharedCheck_1319_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_dec(v___x_1312_);
                        v___x_1314_ = leanh::lean_box(0);
                        v_isShared_1315_ = v_isSharedCheck_1319_;
                        state = 1;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v___y_1309_);
                    v_a_1321_ = leanh::lean_ctor_get(v___x_1312_, 0);
                    v_isSharedCheck_1328_ = (!leanh::lean_is_exclusive(v___x_1312_)) as u8;
                    if v_isSharedCheck_1328_ == 0 {
                        v___x_1323_ = v___x_1312_;
                        v_isShared_1324_ = v_isSharedCheck_1328_;
                        state = 3;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_1321_);
                        leanh::lean_dec(v___x_1312_);
                        v___x_1323_ = leanh::lean_box(0);
                        v_isShared_1324_ = v_isSharedCheck_1328_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_1315_ == 0 {
                    leanh::lean_ctor_set(v___x_1314_, 0, v___y_1309_);
                    v___x_1317_ = v___x_1314_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1318_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1318_, 0, v___y_1309_);
                    v___x_1317_ = v_reuseFailAlloc_1318_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1317_;
            }
            3 => {
                if v_isShared_1324_ == 0 {
                    v___x_1326_ = v___x_1323_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1327_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1327_, 0, v_a_1321_);
                    v___x_1326_ = v_reuseFailAlloc_1327_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_1326_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_instMonadEST___lam__1___boxed(
    mut v_00_u03b1_1329_: *mut leanh::LeanObject,
    mut v_00_u03b2_1330_: *mut leanh::LeanObject,
    mut v___y_1331_: *mut leanh::LeanObject,
    mut v___y_1332_: *mut leanh::LeanObject,
    mut v___y_1333_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1334_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1334_ =
        l_instMonadEST___lam__1(v_00_u03b1_1329_, v_00_u03b2_1330_, v___y_1331_, v___y_1332_);
    return v_res_1334_;
}
pub unsafe fn l_instMonadEST___lam__2(
    mut v_00_u03b1_1335_: *mut leanh::LeanObject,
    mut v___y_1336_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1338_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1338_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_1338_, 0, v___y_1336_);
    return v___x_1338_;
}
pub unsafe fn l_instMonadEST___lam__2___boxed(
    mut v_00_u03b1_1339_: *mut leanh::LeanObject,
    mut v___y_1340_: *mut leanh::LeanObject,
    mut v___y_1341_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1342_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1342_ = l_instMonadEST___lam__2(v_00_u03b1_1339_, v___y_1340_);
    return v_res_1342_;
}
pub unsafe fn l_instMonadEST___lam__3(
    mut v_00_u03b1_1343_: *mut leanh::LeanObject,
    mut v_00_u03b2_1344_: *mut leanh::LeanObject,
    mut v_f_1345_: *mut leanh::LeanObject,
    mut v_x_1346_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1348_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1349_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1350_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1351_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1352_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1354_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1355_: u8 = 0;
    let mut v___x_1356_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1358_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1359_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1360_: u8 = 0;
    let mut v_a_1361_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1363_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1364_: u8 = 0;
    let mut v___x_1366_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1367_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1368_: u8 = 0;
    let mut v_a_1369_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1371_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1372_: u8 = 0;
    let mut v___x_1374_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1375_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1376_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1348_ = leanh::lean_apply_1(v_f_1345_, leanh::lean_box(0));
                if leanh::lean_obj_tag(v___x_1348_) == 0 {
                    v_a_1349_ = leanh::lean_ctor_get(v___x_1348_, 0);
                    leanh::lean_inc(v_a_1349_);
                    leanh::lean_dec_ref_known(v___x_1348_, 1);
                    v___x_1350_ = leanh::lean_box(0);
                    v___x_1351_ = leanh::lean_apply_2(
                        v_x_1346_,
                        v___x_1350_,
                        leanh::lean_box(0),
                    );
                    if leanh::lean_obj_tag(v___x_1351_) == 0 {
                        v_a_1352_ = leanh::lean_ctor_get(v___x_1351_, 0);
                        v_isSharedCheck_1360_ =
                            (!leanh::lean_is_exclusive(v___x_1351_)) as u8;
                        if v_isSharedCheck_1360_ == 0 {
                            v___x_1354_ = v___x_1351_;
                            v_isShared_1355_ = v_isSharedCheck_1360_;
                            state = 1;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_1352_);
                            leanh::lean_dec(v___x_1351_);
                            v___x_1354_ = leanh::lean_box(0);
                            v_isShared_1355_ = v_isSharedCheck_1360_;
                            state = 1;
                            continue;
                        }
                    } else {
                        leanh::lean_dec(v_a_1349_);
                        v_a_1361_ = leanh::lean_ctor_get(v___x_1351_, 0);
                        v_isSharedCheck_1368_ =
                            (!leanh::lean_is_exclusive(v___x_1351_)) as u8;
                        if v_isSharedCheck_1368_ == 0 {
                            v___x_1363_ = v___x_1351_;
                            v_isShared_1364_ = v_isSharedCheck_1368_;
                            state = 3;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_1361_);
                            leanh::lean_dec(v___x_1351_);
                            v___x_1363_ = leanh::lean_box(0);
                            v_isShared_1364_ = v_isSharedCheck_1368_;
                            state = 3;
                            continue;
                        }
                    }
                } else {
                    leanh::lean_dec_ref(v_x_1346_);
                    v_a_1369_ = leanh::lean_ctor_get(v___x_1348_, 0);
                    v_isSharedCheck_1376_ = (!leanh::lean_is_exclusive(v___x_1348_)) as u8;
                    if v_isSharedCheck_1376_ == 0 {
                        v___x_1371_ = v___x_1348_;
                        v_isShared_1372_ = v_isSharedCheck_1376_;
                        state = 5;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_1369_);
                        leanh::lean_dec(v___x_1348_);
                        v___x_1371_ = leanh::lean_box(0);
                        v_isShared_1372_ = v_isSharedCheck_1376_;
                        state = 5;
                        continue;
                    }
                }
            }
            1 => {
                v___x_1356_ = leanh::lean_apply_1(v_a_1349_, v_a_1352_);
                if v_isShared_1355_ == 0 {
                    leanh::lean_ctor_set(v___x_1354_, 0, v___x_1356_);
                    v___x_1358_ = v___x_1354_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1359_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1359_, 0, v___x_1356_);
                    v___x_1358_ = v_reuseFailAlloc_1359_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1358_;
            }
            3 => {
                if v_isShared_1364_ == 0 {
                    v___x_1366_ = v___x_1363_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1367_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1367_, 0, v_a_1361_);
                    v___x_1366_ = v_reuseFailAlloc_1367_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_1366_;
            }
            5 => {
                if v_isShared_1372_ == 0 {
                    v___x_1374_ = v___x_1371_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_1375_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1375_, 0, v_a_1369_);
                    v___x_1374_ = v_reuseFailAlloc_1375_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_1374_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_instMonadEST___lam__3___boxed(
    mut v_00_u03b1_1377_: *mut leanh::LeanObject,
    mut v_00_u03b2_1378_: *mut leanh::LeanObject,
    mut v_f_1379_: *mut leanh::LeanObject,
    mut v_x_1380_: *mut leanh::LeanObject,
    mut v___y_1381_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1382_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1382_ = l_instMonadEST___lam__3(v_00_u03b1_1377_, v_00_u03b2_1378_, v_f_1379_, v_x_1380_);
    return v_res_1382_;
}
pub unsafe fn l_instMonadEST___lam__4(
    mut v_00_u03b1_1383_: *mut leanh::LeanObject,
    mut v_00_u03b2_1384_: *mut leanh::LeanObject,
    mut v_x_1385_: *mut leanh::LeanObject,
    mut v_y_1386_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1388_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1389_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1390_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1391_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1393_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1394_: u8 = 0;
    let mut v___x_1396_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1397_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1398_: u8 = 0;
    let mut v_unused_1399_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1400_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1402_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1403_: u8 = 0;
    let mut v___x_1405_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1406_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1407_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1388_ = leanh::lean_apply_1(v_x_1385_, leanh::lean_box(0));
                if leanh::lean_obj_tag(v___x_1388_) == 0 {
                    v_a_1389_ = leanh::lean_ctor_get(v___x_1388_, 0);
                    leanh::lean_inc(v_a_1389_);
                    leanh::lean_dec_ref_known(v___x_1388_, 1);
                    v___x_1390_ = leanh::lean_box(0);
                    v___x_1391_ = leanh::lean_apply_2(
                        v_y_1386_,
                        v___x_1390_,
                        leanh::lean_box(0),
                    );
                    if leanh::lean_obj_tag(v___x_1391_) == 0 {
                        v_isSharedCheck_1398_ =
                            (!leanh::lean_is_exclusive(v___x_1391_)) as u8;
                        if v_isSharedCheck_1398_ == 0 {
                            v_unused_1399_ = leanh::lean_ctor_get(v___x_1391_, 0);
                            leanh::lean_dec(v_unused_1399_);
                            v___x_1393_ = v___x_1391_;
                            v_isShared_1394_ = v_isSharedCheck_1398_;
                            state = 1;
                            continue;
                        } else {
                            leanh::lean_dec(v___x_1391_);
                            v___x_1393_ = leanh::lean_box(0);
                            v_isShared_1394_ = v_isSharedCheck_1398_;
                            state = 1;
                            continue;
                        }
                    } else {
                        leanh::lean_dec(v_a_1389_);
                        v_a_1400_ = leanh::lean_ctor_get(v___x_1391_, 0);
                        v_isSharedCheck_1407_ =
                            (!leanh::lean_is_exclusive(v___x_1391_)) as u8;
                        if v_isSharedCheck_1407_ == 0 {
                            v___x_1402_ = v___x_1391_;
                            v_isShared_1403_ = v_isSharedCheck_1407_;
                            state = 3;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_1400_);
                            leanh::lean_dec(v___x_1391_);
                            v___x_1402_ = leanh::lean_box(0);
                            v_isShared_1403_ = v_isSharedCheck_1407_;
                            state = 3;
                            continue;
                        }
                    }
                } else {
                    leanh::lean_dec_ref(v_y_1386_);
                    return v___x_1388_;
                }
            }
            1 => {
                if v_isShared_1394_ == 0 {
                    leanh::lean_ctor_set(v___x_1393_, 0, v_a_1389_);
                    v___x_1396_ = v___x_1393_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1397_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1397_, 0, v_a_1389_);
                    v___x_1396_ = v_reuseFailAlloc_1397_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1396_;
            }
            3 => {
                if v_isShared_1403_ == 0 {
                    v___x_1405_ = v___x_1402_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1406_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1406_, 0, v_a_1400_);
                    v___x_1405_ = v_reuseFailAlloc_1406_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_1405_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_instMonadEST___lam__4___boxed(
    mut v_00_u03b1_1408_: *mut leanh::LeanObject,
    mut v_00_u03b2_1409_: *mut leanh::LeanObject,
    mut v_x_1410_: *mut leanh::LeanObject,
    mut v_y_1411_: *mut leanh::LeanObject,
    mut v___y_1412_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1413_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1413_ = l_instMonadEST___lam__4(v_00_u03b1_1408_, v_00_u03b2_1409_, v_x_1410_, v_y_1411_);
    return v_res_1413_;
}
pub unsafe fn l_instMonadEST___lam__5(
    mut v_00_u03b1_1414_: *mut leanh::LeanObject,
    mut v_00_u03b2_1415_: *mut leanh::LeanObject,
    mut v_x_1416_: *mut leanh::LeanObject,
    mut v_y_1417_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1419_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1420_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1421_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1422_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1424_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1425_: u8 = 0;
    let mut v___x_1427_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1428_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1429_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1419_ = leanh::lean_apply_1(v_x_1416_, leanh::lean_box(0));
                if leanh::lean_obj_tag(v___x_1419_) == 0 {
                    leanh::lean_dec_ref_known(v___x_1419_, 1);
                    v___x_1420_ = leanh::lean_box(0);
                    v___x_1421_ = leanh::lean_apply_2(
                        v_y_1417_,
                        v___x_1420_,
                        leanh::lean_box(0),
                    );
                    return v___x_1421_;
                } else {
                    leanh::lean_dec_ref(v_y_1417_);
                    v_a_1422_ = leanh::lean_ctor_get(v___x_1419_, 0);
                    v_isSharedCheck_1429_ = (!leanh::lean_is_exclusive(v___x_1419_)) as u8;
                    if v_isSharedCheck_1429_ == 0 {
                        v___x_1424_ = v___x_1419_;
                        v_isShared_1425_ = v_isSharedCheck_1429_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_1422_);
                        leanh::lean_dec(v___x_1419_);
                        v___x_1424_ = leanh::lean_box(0);
                        v_isShared_1425_ = v_isSharedCheck_1429_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_1425_ == 0 {
                    v___x_1427_ = v___x_1424_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1428_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1428_, 0, v_a_1422_);
                    v___x_1427_ = v_reuseFailAlloc_1428_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1427_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_instMonadEST___lam__5___boxed(
    mut v_00_u03b1_1430_: *mut leanh::LeanObject,
    mut v_00_u03b2_1431_: *mut leanh::LeanObject,
    mut v_x_1432_: *mut leanh::LeanObject,
    mut v_y_1433_: *mut leanh::LeanObject,
    mut v___y_1434_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1435_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1435_ = l_instMonadEST___lam__5(v_00_u03b1_1430_, v_00_u03b2_1431_, v_x_1432_, v_y_1433_);
    return v_res_1435_;
}
pub unsafe fn l_instMonadEST(
    mut v_00_u03b5_1455_: *mut leanh::LeanObject,
    mut v_00_u03c3_1456_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1457_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1457_ = l_instMonadEST___closed__9;
    return v___x_1457_;
}
pub unsafe fn l_instMonadFinallyEST___lam__0(
    mut v_00_u03b1_1458_: *mut leanh::LeanObject,
    mut v_00_u03b2_1459_: *mut leanh::LeanObject,
    mut v_x_1460_: *mut leanh::LeanObject,
    mut v_f_1461_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_r_1463_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1464_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1466_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1467_: u8 = 0;
    let mut v___x_1469_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1470_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1471_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1473_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1474_: u8 = 0;
    let mut v___x_1475_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1477_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1478_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1479_: u8 = 0;
    let mut v_a_1480_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1482_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1483_: u8 = 0;
    let mut v___x_1485_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1486_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1487_: u8 = 0;
    let mut v_reuseFailAlloc_1488_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1489_: u8 = 0;
    let mut v_a_1490_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1491_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1492_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1494_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1495_: u8 = 0;
    let mut v___x_1497_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1498_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1499_: u8 = 0;
    let mut v_unused_1500_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1501_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1503_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1504_: u8 = 0;
    let mut v___x_1506_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1507_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1508_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_r_1463_ = leanh::lean_apply_1(v_x_1460_, leanh::lean_box(0));
                if leanh::lean_obj_tag(v_r_1463_) == 0 {
                    v_a_1464_ = leanh::lean_ctor_get(v_r_1463_, 0);
                    v_isSharedCheck_1489_ = (!leanh::lean_is_exclusive(v_r_1463_)) as u8;
                    if v_isSharedCheck_1489_ == 0 {
                        v___x_1466_ = v_r_1463_;
                        v_isShared_1467_ = v_isSharedCheck_1489_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_1464_);
                        leanh::lean_dec(v_r_1463_);
                        v___x_1466_ = leanh::lean_box(0);
                        v_isShared_1467_ = v_isSharedCheck_1489_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_1490_ = leanh::lean_ctor_get(v_r_1463_, 0);
                    leanh::lean_inc(v_a_1490_);
                    leanh::lean_dec_ref_known(v_r_1463_, 1);
                    v___x_1491_ = leanh::lean_box(0);
                    v___x_1492_ = leanh::lean_apply_2(
                        v_f_1461_,
                        v___x_1491_,
                        leanh::lean_box(0),
                    );
                    if leanh::lean_obj_tag(v___x_1492_) == 0 {
                        v_isSharedCheck_1499_ =
                            (!leanh::lean_is_exclusive(v___x_1492_)) as u8;
                        if v_isSharedCheck_1499_ == 0 {
                            v_unused_1500_ = leanh::lean_ctor_get(v___x_1492_, 0);
                            leanh::lean_dec(v_unused_1500_);
                            v___x_1494_ = v___x_1492_;
                            v_isShared_1495_ = v_isSharedCheck_1499_;
                            state = 7;
                            continue;
                        } else {
                            leanh::lean_dec(v___x_1492_);
                            v___x_1494_ = leanh::lean_box(0);
                            v_isShared_1495_ = v_isSharedCheck_1499_;
                            state = 7;
                            continue;
                        }
                    } else {
                        leanh::lean_dec(v_a_1490_);
                        v_a_1501_ = leanh::lean_ctor_get(v___x_1492_, 0);
                        v_isSharedCheck_1508_ =
                            (!leanh::lean_is_exclusive(v___x_1492_)) as u8;
                        if v_isSharedCheck_1508_ == 0 {
                            v___x_1503_ = v___x_1492_;
                            v_isShared_1504_ = v_isSharedCheck_1508_;
                            state = 9;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_1501_);
                            leanh::lean_dec(v___x_1492_);
                            v___x_1503_ = leanh::lean_box(0);
                            v_isShared_1504_ = v_isSharedCheck_1508_;
                            state = 9;
                            continue;
                        }
                    }
                }
            }
            1 => {
                leanh::lean_inc(v_a_1464_);
                if v_isShared_1467_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_1466_, 1);
                    v___x_1469_ = v___x_1466_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1488_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1488_, 0, v_a_1464_);
                    v___x_1469_ = v_reuseFailAlloc_1488_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_1470_ =
                    leanh::lean_apply_2(v_f_1461_, v___x_1469_, leanh::lean_box(0));
                if leanh::lean_obj_tag(v___x_1470_) == 0 {
                    v_a_1471_ = leanh::lean_ctor_get(v___x_1470_, 0);
                    v_isSharedCheck_1479_ = (!leanh::lean_is_exclusive(v___x_1470_)) as u8;
                    if v_isSharedCheck_1479_ == 0 {
                        v___x_1473_ = v___x_1470_;
                        v_isShared_1474_ = v_isSharedCheck_1479_;
                        state = 3;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_1471_);
                        leanh::lean_dec(v___x_1470_);
                        v___x_1473_ = leanh::lean_box(0);
                        v_isShared_1474_ = v_isSharedCheck_1479_;
                        state = 3;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v_a_1464_);
                    v_a_1480_ = leanh::lean_ctor_get(v___x_1470_, 0);
                    v_isSharedCheck_1487_ = (!leanh::lean_is_exclusive(v___x_1470_)) as u8;
                    if v_isSharedCheck_1487_ == 0 {
                        v___x_1482_ = v___x_1470_;
                        v_isShared_1483_ = v_isSharedCheck_1487_;
                        state = 5;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_1480_);
                        leanh::lean_dec(v___x_1470_);
                        v___x_1482_ = leanh::lean_box(0);
                        v_isShared_1483_ = v_isSharedCheck_1487_;
                        state = 5;
                        continue;
                    }
                }
            }
            3 => {
                v___x_1475_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_1475_, 0, v_a_1464_);
                leanh::lean_ctor_set(v___x_1475_, 1, v_a_1471_);
                if v_isShared_1474_ == 0 {
                    leanh::lean_ctor_set(v___x_1473_, 0, v___x_1475_);
                    v___x_1477_ = v___x_1473_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1478_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1478_, 0, v___x_1475_);
                    v___x_1477_ = v_reuseFailAlloc_1478_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_1477_;
            }
            5 => {
                if v_isShared_1483_ == 0 {
                    v___x_1485_ = v___x_1482_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_1486_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1486_, 0, v_a_1480_);
                    v___x_1485_ = v_reuseFailAlloc_1486_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_1485_;
            }
            7 => {
                if v_isShared_1495_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_1494_, 1);
                    leanh::lean_ctor_set(v___x_1494_, 0, v_a_1490_);
                    v___x_1497_ = v___x_1494_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_1498_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1498_, 0, v_a_1490_);
                    v___x_1497_ = v_reuseFailAlloc_1498_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_1497_;
            }
            9 => {
                if v_isShared_1504_ == 0 {
                    v___x_1506_ = v___x_1503_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_1507_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1507_, 0, v_a_1501_);
                    v___x_1506_ = v_reuseFailAlloc_1507_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_1506_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_instMonadFinallyEST___lam__0___boxed(
    mut v_00_u03b1_1509_: *mut leanh::LeanObject,
    mut v_00_u03b2_1510_: *mut leanh::LeanObject,
    mut v_x_1511_: *mut leanh::LeanObject,
    mut v_f_1512_: *mut leanh::LeanObject,
    mut v_s_1513_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1514_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1514_ =
        l_instMonadFinallyEST___lam__0(v_00_u03b1_1509_, v_00_u03b2_1510_, v_x_1511_, v_f_1512_);
    return v_res_1514_;
}
pub unsafe fn l_instMonadFinallyEST(
    mut v_00_u03b5_1516_: *mut leanh::LeanObject,
    mut v_00_u03c3_1517_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_1518_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_1518_ = l_instMonadFinallyEST___closed__0;
    return v___f_1518_;
}
pub unsafe fn l_instMonadAttachEST___lam__0(
    mut v_00_u03b1_1519_: *mut leanh::LeanObject,
    mut v_x_1520_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1522_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1523_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1525_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1526_: u8 = 0;
    let mut v___x_1528_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1529_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1530_: u8 = 0;
    let mut v_a_1531_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1533_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1534_: u8 = 0;
    let mut v___x_1536_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1537_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1538_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1522_ = leanh::lean_apply_1(v_x_1520_, leanh::lean_box(0));
                if leanh::lean_obj_tag(v___x_1522_) == 0 {
                    v_a_1523_ = leanh::lean_ctor_get(v___x_1522_, 0);
                    v_isSharedCheck_1530_ = (!leanh::lean_is_exclusive(v___x_1522_)) as u8;
                    if v_isSharedCheck_1530_ == 0 {
                        v___x_1525_ = v___x_1522_;
                        v_isShared_1526_ = v_isSharedCheck_1530_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_1523_);
                        leanh::lean_dec(v___x_1522_);
                        v___x_1525_ = leanh::lean_box(0);
                        v_isShared_1526_ = v_isSharedCheck_1530_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_1531_ = leanh::lean_ctor_get(v___x_1522_, 0);
                    v_isSharedCheck_1538_ = (!leanh::lean_is_exclusive(v___x_1522_)) as u8;
                    if v_isSharedCheck_1538_ == 0 {
                        v___x_1533_ = v___x_1522_;
                        v_isShared_1534_ = v_isSharedCheck_1538_;
                        state = 3;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_1531_);
                        leanh::lean_dec(v___x_1522_);
                        v___x_1533_ = leanh::lean_box(0);
                        v_isShared_1534_ = v_isSharedCheck_1538_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_1526_ == 0 {
                    v___x_1528_ = v___x_1525_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1529_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1529_, 0, v_a_1523_);
                    v___x_1528_ = v_reuseFailAlloc_1529_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1528_;
            }
            3 => {
                if v_isShared_1534_ == 0 {
                    v___x_1536_ = v___x_1533_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1537_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1537_, 0, v_a_1531_);
                    v___x_1536_ = v_reuseFailAlloc_1537_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_1536_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_instMonadAttachEST___lam__0___boxed(
    mut v_00_u03b1_1539_: *mut leanh::LeanObject,
    mut v_x_1540_: *mut leanh::LeanObject,
    mut v_s_1541_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1542_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1542_ = l_instMonadAttachEST___lam__0(v_00_u03b1_1539_, v_x_1540_);
    return v_res_1542_;
}
pub unsafe fn l_instMonadAttachEST(
    mut v_00_u03b5_1544_: *mut leanh::LeanObject,
    mut v_00_u03c3_1545_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_1546_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_1546_ = l_instMonadAttachEST___closed__0;
    return v___f_1546_;
}
pub unsafe fn l_instMonadExceptOfEST(
    mut v_00_u03b5_1552_: *mut leanh::LeanObject,
    mut v_00_u03c3_1553_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1554_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1554_ = l_instMonadExceptOfEST___closed__2;
    return v___x_1554_;
}
pub unsafe fn l_instInhabitedEST___redArg___lam__0(
    mut v_inst_1555_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1557_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1557_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_1557_, 0, v_inst_1555_);
    return v___x_1557_;
}
pub unsafe fn l_instInhabitedEST___redArg___lam__0___boxed(
    mut v_inst_1558_: *mut leanh::LeanObject,
    mut v_s_1559_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1560_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1560_ = l_instInhabitedEST___redArg___lam__0(v_inst_1558_);
    return v_res_1560_;
}
pub unsafe fn l_instInhabitedEST___redArg(
    mut v_inst_1561_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_1562_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_1562_ = leanh::lean_alloc_closure(
        l_instInhabitedEST___redArg___lam__0___boxed as *mut core::ffi::c_void,
        2,
        1,
    );
    leanh::lean_closure_set(v___f_1562_, 0, v_inst_1561_);
    return v___f_1562_;
}
pub unsafe fn l_instInhabitedEST(
    mut v_00_u03b5_1563_: *mut leanh::LeanObject,
    mut v_00_u03c3_1564_: *mut leanh::LeanObject,
    mut v_00_u03b1_1565_: *mut leanh::LeanObject,
    mut v_inst_1566_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_1567_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_1567_ = leanh::lean_alloc_closure(
        l_instInhabitedEST___redArg___lam__0___boxed as *mut core::ffi::c_void,
        2,
        1,
    );
    leanh::lean_closure_set(v___f_1567_, 0, v_inst_1566_);
    return v___f_1567_;
}
pub unsafe fn l_instSTWorldOfMonadLift(
    mut v_00_u03c3_1568_: *mut leanh::LeanObject,
    mut v_m_1569_: *mut leanh::LeanObject,
    mut v_n_1570_: *mut leanh::LeanObject,
    mut v_inst_1571_: *mut leanh::LeanObject,
    mut v_inst_1572_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1573_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1573_ = leanh::lean_box(0);
    return v___x_1573_;
}
pub unsafe fn l_instSTWorldOfMonadLift___boxed(
    mut v_00_u03c3_1574_: *mut leanh::LeanObject,
    mut v_m_1575_: *mut leanh::LeanObject,
    mut v_n_1576_: *mut leanh::LeanObject,
    mut v_inst_1577_: *mut leanh::LeanObject,
    mut v_inst_1578_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1579_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1579_ = l_instSTWorldOfMonadLift(
        v_00_u03c3_1574_,
        v_m_1575_,
        v_n_1576_,
        v_inst_1577_,
        v_inst_1578_,
    );
    leanh::lean_dec(v_inst_1577_);
    return v_res_1579_;
}
pub unsafe fn l_instSTWorldST(
    mut v_00_u03c3_1580_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1581_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1581_ = leanh::lean_box(0);
    return v___x_1581_;
}
pub unsafe fn l_instSTWorldEST(
    mut v_00_u03b5_1582_: *mut leanh::LeanObject,
    mut v_00_u03c3_1583_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1584_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1584_ = leanh::lean_box(0);
    return v___x_1584_;
}
pub unsafe fn l_runEST___redArg(
    mut v_x_1585_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1586_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1587_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1588_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1589_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1591_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1592_: u8 = 0;
    let mut v___x_1594_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1595_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1596_: u8 = 0;
    let mut v_a_1597_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1599_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1600_: u8 = 0;
    let mut v___x_1602_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1603_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1604_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1586_ = leanh::lean_box(0);
                v___x_1587_ = lean_void_mk(v___x_1586_);
                v___x_1588_ =
                    leanh::lean_apply_2(v_x_1585_, leanh::lean_box(0), v___x_1587_);
                if leanh::lean_obj_tag(v___x_1588_) == 0 {
                    v_a_1589_ = leanh::lean_ctor_get(v___x_1588_, 0);
                    v_isSharedCheck_1596_ = (!leanh::lean_is_exclusive(v___x_1588_)) as u8;
                    if v_isSharedCheck_1596_ == 0 {
                        v___x_1591_ = v___x_1588_;
                        v_isShared_1592_ = v_isSharedCheck_1596_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_1589_);
                        leanh::lean_dec(v___x_1588_);
                        v___x_1591_ = leanh::lean_box(0);
                        v_isShared_1592_ = v_isSharedCheck_1596_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_1597_ = leanh::lean_ctor_get(v___x_1588_, 0);
                    v_isSharedCheck_1604_ = (!leanh::lean_is_exclusive(v___x_1588_)) as u8;
                    if v_isSharedCheck_1604_ == 0 {
                        v___x_1599_ = v___x_1588_;
                        v_isShared_1600_ = v_isSharedCheck_1604_;
                        state = 3;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_1597_);
                        leanh::lean_dec(v___x_1588_);
                        v___x_1599_ = leanh::lean_box(0);
                        v_isShared_1600_ = v_isSharedCheck_1604_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_1592_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_1591_, 1);
                    v___x_1594_ = v___x_1591_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1595_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1595_, 0, v_a_1589_);
                    v___x_1594_ = v_reuseFailAlloc_1595_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1594_;
            }
            3 => {
                if v_isShared_1600_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_1599_, 0);
                    v___x_1602_ = v___x_1599_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1603_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1603_, 0, v_a_1597_);
                    v___x_1602_ = v_reuseFailAlloc_1603_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_1602_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_runEST(
    mut v_00_u03b5_1605_: *mut leanh::LeanObject,
    mut v_00_u03b1_1606_: *mut leanh::LeanObject,
    mut v_x_1607_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1608_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1608_ = l_runEST___redArg(v_x_1607_);
    return v___x_1608_;
}
pub unsafe fn l_runST___redArg(
    mut v_x_1609_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1610_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1611_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1612_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1610_ = leanh::lean_box(0);
    v___x_1611_ = lean_void_mk(v___x_1610_);
    v___x_1612_ = leanh::lean_apply_2(v_x_1609_, leanh::lean_box(0), v___x_1611_);
    return v___x_1612_;
}
pub unsafe fn l_runST(
    mut v_00_u03b1_1613_: *mut leanh::LeanObject,
    mut v_x_1614_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1615_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1615_ = l_runST___redArg(v_x_1614_);
    return v___x_1615_;
}
pub unsafe fn l_instMonadLiftSTEST___lam__0(
    mut v_00_u03b1_1616_: *mut leanh::LeanObject,
    mut v_x_1617_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1619_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1620_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1619_ = leanh::lean_apply_1(v_x_1617_, leanh::lean_box(0));
    v___x_1620_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_1620_, 0, v___x_1619_);
    return v___x_1620_;
}
pub unsafe fn l_instMonadLiftSTEST___lam__0___boxed(
    mut v_00_u03b1_1621_: *mut leanh::LeanObject,
    mut v_x_1622_: *mut leanh::LeanObject,
    mut v_s_1623_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1624_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1624_ = l_instMonadLiftSTEST___lam__0(v_00_u03b1_1621_, v_x_1622_);
    return v_res_1624_;
}
pub unsafe fn l_instMonadLiftSTEST(
    mut v_00_u03b5_1626_: *mut leanh::LeanObject,
    mut v_00_u03c3_1627_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_1628_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_1628_ = l_instMonadLiftSTEST___closed__0;
    return v___f_1628_;
}
pub unsafe fn _init_l_ST_RefPointed() -> *mut leanh::LeanObject {
    let mut v___x_1629_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1629_ = leanh::lean_box(0);
    return v___x_1629_;
}
pub unsafe fn l_ST_Prim_mkRef___boxed(
    mut v_00_u03c3_1634_: *mut leanh::LeanObject,
    mut v_00_u03b1_1635_: *mut leanh::LeanObject,
    mut v_a_1636_: *mut leanh::LeanObject,
    mut v_a_00___x40___internal___hyg_1637_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1638_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1638_ = lean_st_mk_ref(v_a_1636_);
    return v_res_1638_;
}
pub unsafe fn l_ST_Prim_Ref_get___boxed(
    mut v_00_u03c3_1643_: *mut leanh::LeanObject,
    mut v_00_u03b1_1644_: *mut leanh::LeanObject,
    mut v_r_1645_: *mut leanh::LeanObject,
    mut v_a_00___x40___internal___hyg_1646_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1647_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1647_ = lean_st_ref_get(v_r_1645_);
    leanh::lean_dec(v_r_1645_);
    return v_res_1647_;
}
pub unsafe fn l_ST_Prim_Ref_set___boxed(
    mut v_00_u03c3_1653_: *mut leanh::LeanObject,
    mut v_00_u03b1_1654_: *mut leanh::LeanObject,
    mut v_r_1655_: *mut leanh::LeanObject,
    mut v_a_1656_: *mut leanh::LeanObject,
    mut v_a_00___x40___internal___hyg_1657_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1658_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1658_ = lean_st_ref_set(v_r_1655_, v_a_1656_);
    leanh::lean_dec(v_r_1655_);
    return v_res_1658_;
}
pub unsafe fn l_ST_Prim_Ref_swap___boxed(
    mut v_00_u03c3_1664_: *mut leanh::LeanObject,
    mut v_00_u03b1_1665_: *mut leanh::LeanObject,
    mut v_r_1666_: *mut leanh::LeanObject,
    mut v_a_1667_: *mut leanh::LeanObject,
    mut v_a_00___x40___internal___hyg_1668_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1669_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1669_ = lean_st_ref_swap(v_r_1666_, v_a_1667_);
    leanh::lean_dec(v_r_1666_);
    return v_res_1669_;
}
pub unsafe fn l_ST_Prim_Ref_take___boxed(
    mut v_00_u03c3_1674_: *mut leanh::LeanObject,
    mut v_00_u03b1_1675_: *mut leanh::LeanObject,
    mut v_r_1676_: *mut leanh::LeanObject,
    mut v_a_00___x40___internal___hyg_1677_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1678_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1678_ = lean_st_ref_take(v_r_1676_);
    leanh::lean_dec(v_r_1676_);
    return v_res_1678_;
}
pub unsafe fn l_ST_Prim_Ref_ptrEq___boxed(
    mut v_00_u03c3_1684_: *mut leanh::LeanObject,
    mut v_00_u03b1_1685_: *mut leanh::LeanObject,
    mut v_r1_1686_: *mut leanh::LeanObject,
    mut v_r2_1687_: *mut leanh::LeanObject,
    mut v_a_00___x40___internal___hyg_1688_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1689_: u8 = 0;
    let mut v_r_1690_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1689_ = lean_st_ref_ptr_eq(v_r1_1686_, v_r2_1687_);
    leanh::lean_dec(v_r2_1687_);
    leanh::lean_dec(v_r1_1686_);
    v_r_1690_ = leanh::lean_box((v_res_1689_) as usize);
    return v_r_1690_;
}
pub unsafe fn l_ST_Prim_Ref_modifyUnsafe___redArg(
    mut v_r_1691_: *mut leanh::LeanObject,
    mut v_f_1692_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1694_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1695_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1696_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1694_ = lean_st_ref_take(v_r_1691_);
    v___x_1695_ = leanh::lean_apply_1(v_f_1692_, v___x_1694_);
    v___x_1696_ = lean_st_ref_set(v_r_1691_, v___x_1695_);
    return v___x_1696_;
}
pub unsafe fn l_ST_Prim_Ref_modifyUnsafe___redArg___boxed(
    mut v_r_1697_: *mut leanh::LeanObject,
    mut v_f_1698_: *mut leanh::LeanObject,
    mut v_a_1699_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1700_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1700_ = l_ST_Prim_Ref_modifyUnsafe___redArg(v_r_1697_, v_f_1698_);
    leanh::lean_dec(v_r_1697_);
    return v_res_1700_;
}
pub unsafe fn l_ST_Prim_Ref_modifyUnsafe(
    mut v_00_u03c3_1701_: *mut leanh::LeanObject,
    mut v_00_u03b1_1702_: *mut leanh::LeanObject,
    mut v_r_1703_: *mut leanh::LeanObject,
    mut v_f_1704_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1706_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1707_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1708_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1706_ = lean_st_ref_take(v_r_1703_);
    v___x_1707_ = leanh::lean_apply_1(v_f_1704_, v___x_1706_);
    v___x_1708_ = lean_st_ref_set(v_r_1703_, v___x_1707_);
    return v___x_1708_;
}
pub unsafe fn l_ST_Prim_Ref_modifyUnsafe___boxed(
    mut v_00_u03c3_1709_: *mut leanh::LeanObject,
    mut v_00_u03b1_1710_: *mut leanh::LeanObject,
    mut v_r_1711_: *mut leanh::LeanObject,
    mut v_f_1712_: *mut leanh::LeanObject,
    mut v_a_1713_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1714_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1714_ =
        l_ST_Prim_Ref_modifyUnsafe(v_00_u03c3_1709_, v_00_u03b1_1710_, v_r_1711_, v_f_1712_);
    leanh::lean_dec(v_r_1711_);
    return v_res_1714_;
}
pub unsafe fn l_ST_Prim_Ref_modifyGetUnsafe___redArg(
    mut v_r_1715_: *mut leanh::LeanObject,
    mut v_f_1716_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1718_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1719_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_1720_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_1721_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1722_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1718_ = lean_st_ref_take(v_r_1715_);
    v___x_1719_ = leanh::lean_apply_1(v_f_1716_, v___x_1718_);
    v_fst_1720_ = leanh::lean_ctor_get(v___x_1719_, 0);
    leanh::lean_inc(v_fst_1720_);
    v_snd_1721_ = leanh::lean_ctor_get(v___x_1719_, 1);
    leanh::lean_inc(v_snd_1721_);
    leanh::lean_dec_ref(v___x_1719_);
    v___x_1722_ = lean_st_ref_set(v_r_1715_, v_snd_1721_);
    return v_fst_1720_;
}
pub unsafe fn l_ST_Prim_Ref_modifyGetUnsafe___redArg___boxed(
    mut v_r_1723_: *mut leanh::LeanObject,
    mut v_f_1724_: *mut leanh::LeanObject,
    mut v_a_1725_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1726_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1726_ = l_ST_Prim_Ref_modifyGetUnsafe___redArg(v_r_1723_, v_f_1724_);
    leanh::lean_dec(v_r_1723_);
    return v_res_1726_;
}
pub unsafe fn l_ST_Prim_Ref_modifyGetUnsafe(
    mut v_00_u03c3_1727_: *mut leanh::LeanObject,
    mut v_00_u03b1_1728_: *mut leanh::LeanObject,
    mut v_00_u03b2_1729_: *mut leanh::LeanObject,
    mut v_r_1730_: *mut leanh::LeanObject,
    mut v_f_1731_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1733_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1734_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_1735_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_1736_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1737_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1733_ = lean_st_ref_take(v_r_1730_);
    v___x_1734_ = leanh::lean_apply_1(v_f_1731_, v___x_1733_);
    v_fst_1735_ = leanh::lean_ctor_get(v___x_1734_, 0);
    leanh::lean_inc(v_fst_1735_);
    v_snd_1736_ = leanh::lean_ctor_get(v___x_1734_, 1);
    leanh::lean_inc(v_snd_1736_);
    leanh::lean_dec_ref(v___x_1734_);
    v___x_1737_ = lean_st_ref_set(v_r_1730_, v_snd_1736_);
    return v_fst_1735_;
}
pub unsafe fn l_ST_Prim_Ref_modifyGetUnsafe___boxed(
    mut v_00_u03c3_1738_: *mut leanh::LeanObject,
    mut v_00_u03b1_1739_: *mut leanh::LeanObject,
    mut v_00_u03b2_1740_: *mut leanh::LeanObject,
    mut v_r_1741_: *mut leanh::LeanObject,
    mut v_f_1742_: *mut leanh::LeanObject,
    mut v_a_1743_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1744_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1744_ = l_ST_Prim_Ref_modifyGetUnsafe(
        v_00_u03c3_1738_,
        v_00_u03b1_1739_,
        v_00_u03b2_1740_,
        v_r_1741_,
        v_f_1742_,
    );
    leanh::lean_dec(v_r_1741_);
    return v_res_1744_;
}
pub unsafe fn l_ST_mkRef___redArg(
    mut v_inst_1745_: *mut leanh::LeanObject,
    mut v_a_1746_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1747_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1748_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1747_ =
        leanh::lean_alloc_closure(l_ST_Prim_mkRef___boxed as *mut core::ffi::c_void, 4, 3);
    leanh::lean_closure_set(v___x_1747_, 0, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_1747_, 1, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_1747_, 2, v_a_1746_);
    v___x_1748_ = leanh::lean_apply_2(v_inst_1745_, leanh::lean_box(0), v___x_1747_);
    return v___x_1748_;
}
pub unsafe fn l_ST_mkRef(
    mut v_00_u03c3_1749_: *mut leanh::LeanObject,
    mut v_m_1750_: *mut leanh::LeanObject,
    mut v_inst_1751_: *mut leanh::LeanObject,
    mut v_00_u03b1_1752_: *mut leanh::LeanObject,
    mut v_a_1753_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1754_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1755_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1754_ =
        leanh::lean_alloc_closure(l_ST_Prim_mkRef___boxed as *mut core::ffi::c_void, 4, 3);
    leanh::lean_closure_set(v___x_1754_, 0, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_1754_, 1, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_1754_, 2, v_a_1753_);
    v___x_1755_ = leanh::lean_apply_2(v_inst_1751_, leanh::lean_box(0), v___x_1754_);
    return v___x_1755_;
}
pub unsafe fn l_ST_Ref_get___redArg(
    mut v_inst_1756_: *mut leanh::LeanObject,
    mut v_r_1757_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1758_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1759_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1758_ =
        leanh::lean_alloc_closure(l_ST_Prim_Ref_get___boxed as *mut core::ffi::c_void, 4, 3);
    leanh::lean_closure_set(v___x_1758_, 0, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_1758_, 1, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_1758_, 2, v_r_1757_);
    v___x_1759_ = leanh::lean_apply_2(v_inst_1756_, leanh::lean_box(0), v___x_1758_);
    return v___x_1759_;
}
pub unsafe fn l_ST_Ref_get(
    mut v_00_u03c3_1760_: *mut leanh::LeanObject,
    mut v_m_1761_: *mut leanh::LeanObject,
    mut v_inst_1762_: *mut leanh::LeanObject,
    mut v_00_u03b1_1763_: *mut leanh::LeanObject,
    mut v_r_1764_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1765_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1766_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1765_ =
        leanh::lean_alloc_closure(l_ST_Prim_Ref_get___boxed as *mut core::ffi::c_void, 4, 3);
    leanh::lean_closure_set(v___x_1765_, 0, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_1765_, 1, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_1765_, 2, v_r_1764_);
    v___x_1766_ = leanh::lean_apply_2(v_inst_1762_, leanh::lean_box(0), v___x_1765_);
    return v___x_1766_;
}
pub unsafe fn l_ST_Ref_set___redArg(
    mut v_inst_1767_: *mut leanh::LeanObject,
    mut v_r_1768_: *mut leanh::LeanObject,
    mut v_a_1769_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1770_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1771_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1770_ =
        leanh::lean_alloc_closure(l_ST_Prim_Ref_set___boxed as *mut core::ffi::c_void, 5, 4);
    leanh::lean_closure_set(v___x_1770_, 0, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_1770_, 1, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_1770_, 2, v_r_1768_);
    leanh::lean_closure_set(v___x_1770_, 3, v_a_1769_);
    v___x_1771_ = leanh::lean_apply_2(v_inst_1767_, leanh::lean_box(0), v___x_1770_);
    return v___x_1771_;
}
pub unsafe fn l_ST_Ref_set(
    mut v_00_u03c3_1772_: *mut leanh::LeanObject,
    mut v_m_1773_: *mut leanh::LeanObject,
    mut v_inst_1774_: *mut leanh::LeanObject,
    mut v_00_u03b1_1775_: *mut leanh::LeanObject,
    mut v_r_1776_: *mut leanh::LeanObject,
    mut v_a_1777_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1778_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1779_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1778_ =
        leanh::lean_alloc_closure(l_ST_Prim_Ref_set___boxed as *mut core::ffi::c_void, 5, 4);
    leanh::lean_closure_set(v___x_1778_, 0, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_1778_, 1, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_1778_, 2, v_r_1776_);
    leanh::lean_closure_set(v___x_1778_, 3, v_a_1777_);
    v___x_1779_ = leanh::lean_apply_2(v_inst_1774_, leanh::lean_box(0), v___x_1778_);
    return v___x_1779_;
}
pub unsafe fn l_ST_Ref_swap___redArg(
    mut v_inst_1780_: *mut leanh::LeanObject,
    mut v_r_1781_: *mut leanh::LeanObject,
    mut v_a_1782_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1783_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1784_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1783_ = leanh::lean_alloc_closure(
        l_ST_Prim_Ref_swap___boxed as *mut core::ffi::c_void,
        5,
        4,
    );
    leanh::lean_closure_set(v___x_1783_, 0, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_1783_, 1, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_1783_, 2, v_r_1781_);
    leanh::lean_closure_set(v___x_1783_, 3, v_a_1782_);
    v___x_1784_ = leanh::lean_apply_2(v_inst_1780_, leanh::lean_box(0), v___x_1783_);
    return v___x_1784_;
}
pub unsafe fn l_ST_Ref_swap(
    mut v_00_u03c3_1785_: *mut leanh::LeanObject,
    mut v_m_1786_: *mut leanh::LeanObject,
    mut v_inst_1787_: *mut leanh::LeanObject,
    mut v_00_u03b1_1788_: *mut leanh::LeanObject,
    mut v_r_1789_: *mut leanh::LeanObject,
    mut v_a_1790_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1791_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1792_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1791_ = leanh::lean_alloc_closure(
        l_ST_Prim_Ref_swap___boxed as *mut core::ffi::c_void,
        5,
        4,
    );
    leanh::lean_closure_set(v___x_1791_, 0, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_1791_, 1, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_1791_, 2, v_r_1789_);
    leanh::lean_closure_set(v___x_1791_, 3, v_a_1790_);
    v___x_1792_ = leanh::lean_apply_2(v_inst_1787_, leanh::lean_box(0), v___x_1791_);
    return v___x_1792_;
}
pub unsafe fn l_ST_Ref_take___redArg(
    mut v_inst_1793_: *mut leanh::LeanObject,
    mut v_r_1794_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1795_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1796_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1795_ = leanh::lean_alloc_closure(
        l_ST_Prim_Ref_take___boxed as *mut core::ffi::c_void,
        4,
        3,
    );
    leanh::lean_closure_set(v___x_1795_, 0, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_1795_, 1, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_1795_, 2, v_r_1794_);
    v___x_1796_ = leanh::lean_apply_2(v_inst_1793_, leanh::lean_box(0), v___x_1795_);
    return v___x_1796_;
}
pub unsafe fn l_ST_Ref_take(
    mut v_00_u03c3_1797_: *mut leanh::LeanObject,
    mut v_m_1798_: *mut leanh::LeanObject,
    mut v_inst_1799_: *mut leanh::LeanObject,
    mut v_00_u03b1_1800_: *mut leanh::LeanObject,
    mut v_r_1801_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1802_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1803_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1802_ = leanh::lean_alloc_closure(
        l_ST_Prim_Ref_take___boxed as *mut core::ffi::c_void,
        4,
        3,
    );
    leanh::lean_closure_set(v___x_1802_, 0, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_1802_, 1, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_1802_, 2, v_r_1801_);
    v___x_1803_ = leanh::lean_apply_2(v_inst_1799_, leanh::lean_box(0), v___x_1802_);
    return v___x_1803_;
}
pub unsafe fn l_ST_Ref_ptrEq___redArg(
    mut v_inst_1804_: *mut leanh::LeanObject,
    mut v_r1_1805_: *mut leanh::LeanObject,
    mut v_r2_1806_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1807_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1808_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1807_ = leanh::lean_alloc_closure(
        l_ST_Prim_Ref_ptrEq___boxed as *mut core::ffi::c_void,
        5,
        4,
    );
    leanh::lean_closure_set(v___x_1807_, 0, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_1807_, 1, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_1807_, 2, v_r1_1805_);
    leanh::lean_closure_set(v___x_1807_, 3, v_r2_1806_);
    v___x_1808_ = leanh::lean_apply_2(v_inst_1804_, leanh::lean_box(0), v___x_1807_);
    return v___x_1808_;
}
pub unsafe fn l_ST_Ref_ptrEq(
    mut v_00_u03c3_1809_: *mut leanh::LeanObject,
    mut v_m_1810_: *mut leanh::LeanObject,
    mut v_inst_1811_: *mut leanh::LeanObject,
    mut v_00_u03b1_1812_: *mut leanh::LeanObject,
    mut v_r1_1813_: *mut leanh::LeanObject,
    mut v_r2_1814_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1815_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1816_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1815_ = leanh::lean_alloc_closure(
        l_ST_Prim_Ref_ptrEq___boxed as *mut core::ffi::c_void,
        5,
        4,
    );
    leanh::lean_closure_set(v___x_1815_, 0, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_1815_, 1, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_1815_, 2, v_r1_1813_);
    leanh::lean_closure_set(v___x_1815_, 3, v_r2_1814_);
    v___x_1816_ = leanh::lean_apply_2(v_inst_1811_, leanh::lean_box(0), v___x_1815_);
    return v___x_1816_;
}
pub unsafe fn l_ST_Ref_modify___redArg(
    mut v_inst_1817_: *mut leanh::LeanObject,
    mut v_r_1818_: *mut leanh::LeanObject,
    mut v_f_1819_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1820_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1821_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1820_ = leanh::lean_alloc_closure(
        l_ST_Prim_Ref_modifyUnsafe___boxed as *mut core::ffi::c_void,
        5,
        4,
    );
    leanh::lean_closure_set(v___x_1820_, 0, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_1820_, 1, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_1820_, 2, v_r_1818_);
    leanh::lean_closure_set(v___x_1820_, 3, v_f_1819_);
    v___x_1821_ = leanh::lean_apply_2(v_inst_1817_, leanh::lean_box(0), v___x_1820_);
    return v___x_1821_;
}
pub unsafe fn l_ST_Ref_modify(
    mut v_00_u03c3_1822_: *mut leanh::LeanObject,
    mut v_m_1823_: *mut leanh::LeanObject,
    mut v_inst_1824_: *mut leanh::LeanObject,
    mut v_00_u03b1_1825_: *mut leanh::LeanObject,
    mut v_r_1826_: *mut leanh::LeanObject,
    mut v_f_1827_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1828_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1829_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1828_ = leanh::lean_alloc_closure(
        l_ST_Prim_Ref_modifyUnsafe___boxed as *mut core::ffi::c_void,
        5,
        4,
    );
    leanh::lean_closure_set(v___x_1828_, 0, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_1828_, 1, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_1828_, 2, v_r_1826_);
    leanh::lean_closure_set(v___x_1828_, 3, v_f_1827_);
    v___x_1829_ = leanh::lean_apply_2(v_inst_1824_, leanh::lean_box(0), v___x_1828_);
    return v___x_1829_;
}
pub unsafe fn l_ST_Ref_modifyGet___redArg(
    mut v_inst_1830_: *mut leanh::LeanObject,
    mut v_r_1831_: *mut leanh::LeanObject,
    mut v_f_1832_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1833_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1834_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1833_ = leanh::lean_alloc_closure(
        l_ST_Prim_Ref_modifyGetUnsafe___boxed as *mut core::ffi::c_void,
        6,
        5,
    );
    leanh::lean_closure_set(v___x_1833_, 0, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_1833_, 1, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_1833_, 2, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_1833_, 3, v_r_1831_);
    leanh::lean_closure_set(v___x_1833_, 4, v_f_1832_);
    v___x_1834_ = leanh::lean_apply_2(v_inst_1830_, leanh::lean_box(0), v___x_1833_);
    return v___x_1834_;
}
pub unsafe fn l_ST_Ref_modifyGet(
    mut v_00_u03c3_1835_: *mut leanh::LeanObject,
    mut v_m_1836_: *mut leanh::LeanObject,
    mut v_inst_1837_: *mut leanh::LeanObject,
    mut v_00_u03b1_1838_: *mut leanh::LeanObject,
    mut v_00_u03b2_1839_: *mut leanh::LeanObject,
    mut v_r_1840_: *mut leanh::LeanObject,
    mut v_f_1841_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1842_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1843_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1842_ = leanh::lean_alloc_closure(
        l_ST_Prim_Ref_modifyGetUnsafe___boxed as *mut core::ffi::c_void,
        6,
        5,
    );
    leanh::lean_closure_set(v___x_1842_, 0, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_1842_, 1, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_1842_, 2, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_1842_, 3, v_r_1840_);
    leanh::lean_closure_set(v___x_1842_, 4, v_f_1841_);
    v___x_1843_ = leanh::lean_apply_2(v_inst_1837_, leanh::lean_box(0), v___x_1842_);
    return v___x_1843_;
}
pub unsafe fn l_ST_Ref_toMonadStateOf___redArg___lam__0(
    mut v_r_1844_: *mut leanh::LeanObject,
    mut v_inst_1845_: *mut leanh::LeanObject,
    mut v_00_u03b1_1846_: *mut leanh::LeanObject,
    mut v___y_1847_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1848_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1849_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1848_ = leanh::lean_alloc_closure(
        l_ST_Prim_Ref_modifyGetUnsafe___boxed as *mut core::ffi::c_void,
        6,
        5,
    );
    leanh::lean_closure_set(v___x_1848_, 0, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_1848_, 1, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_1848_, 2, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_1848_, 3, v_r_1844_);
    leanh::lean_closure_set(v___x_1848_, 4, v___y_1847_);
    v___x_1849_ = leanh::lean_apply_2(v_inst_1845_, leanh::lean_box(0), v___x_1848_);
    return v___x_1849_;
}
pub unsafe fn l_ST_Ref_toMonadStateOf___redArg(
    mut v_inst_1850_: *mut leanh::LeanObject,
    mut v_r_1851_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_1852_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1853_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1854_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1855_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1856_: *mut leanh::LeanObject = core::ptr::null_mut();
    leanh::lean_inc_n(v_inst_1850_, 2);
    leanh::lean_inc_n(v_r_1851_, 2);
    v___f_1852_ = leanh::lean_alloc_closure(
        l_ST_Ref_toMonadStateOf___redArg___lam__0 as *mut core::ffi::c_void,
        4,
        2,
    );
    leanh::lean_closure_set(v___f_1852_, 0, v_r_1851_);
    leanh::lean_closure_set(v___f_1852_, 1, v_inst_1850_);
    v___x_1853_ =
        leanh::lean_alloc_closure(l_ST_Prim_Ref_get___boxed as *mut core::ffi::c_void, 4, 3);
    leanh::lean_closure_set(v___x_1853_, 0, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_1853_, 1, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_1853_, 2, v_r_1851_);
    v___x_1854_ = leanh::lean_apply_2(v_inst_1850_, leanh::lean_box(0), v___x_1853_);
    v___x_1855_ = leanh::lean_alloc_closure(l_ST_Ref_set as *mut core::ffi::c_void, 6, 5);
    leanh::lean_closure_set(v___x_1855_, 0, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_1855_, 1, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_1855_, 2, v_inst_1850_);
    leanh::lean_closure_set(v___x_1855_, 3, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_1855_, 4, v_r_1851_);
    v___x_1856_ = leanh::lean_alloc_ctor(0, 3, (0) as u32);
    leanh::lean_ctor_set(v___x_1856_, 0, v___x_1854_);
    leanh::lean_ctor_set(v___x_1856_, 1, v___x_1855_);
    leanh::lean_ctor_set(v___x_1856_, 2, v___f_1852_);
    return v___x_1856_;
}
pub unsafe fn l_ST_Ref_toMonadStateOf(
    mut v_00_u03c3_1857_: *mut leanh::LeanObject,
    mut v_m_1858_: *mut leanh::LeanObject,
    mut v_inst_1859_: *mut leanh::LeanObject,
    mut v_00_u03b1_1860_: *mut leanh::LeanObject,
    mut v_r_1861_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1862_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1862_ = l_ST_Ref_toMonadStateOf___redArg(v_inst_1859_, v_r_1861_);
    return v___x_1862_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Init_System_ST(builtin: u8) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Init_Control_Except(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_NotationExtra(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Classical(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    l_ST_RefPointed = _init_l_ST_RefPointed();
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Init_System_ST(builtin: u8) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_meta_initialized = true;
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Init_System_ST(builtin: u8) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Init_Control_Except(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Init_NotationExtra(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Init_Classical(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_System_ST(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = meta_initialize_Init_System_ST(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return initialize_Init_System_ST(builtin);
}